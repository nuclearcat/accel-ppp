/*
 * poolng.c
 * Alternative IP pool manager
 * Author: Denys Fedoryshchenko <denys.f@collabora.com>
 * TODO:
 * - add support for /30 blocks and arbitrary netmask/step
 * - add support for IPv6
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <string.h>
#include <arpa/inet.h>
#include <regex.h>

#include "events.h"
#include "log.h"
#include "list.h"
#include "spinlock.h"
#include "backup.h"
#include "ap_session_backup.h"

#include "ipdb.h"

#ifdef RADIUS
#include "radius.h"
#endif

#include "memdebug.h"

#ifdef RADIUS
static int conf_vendor = 0;
static int conf_attr = 88; // Framed-Pool
#endif

static struct ipdb_t ipdb;

struct range_t {
	uint32_t start;
	uint32_t count;
	uint32_t gw;
	struct range_t *next;
};

struct pool_t {
	char name[64];
	uint8_t *bitmap;
	uint32_t bitmap_size;
	struct range_t *range;
	struct ipv4db_item_t **allocated_its;
};

struct pool_t *pools;
size_t pools_count = 0;

int find_free_bit(uint8_t *bitmap, size_t size) {
	for (size_t i = 0; i < size / 8; i++) {
		if (bitmap[i] != 0xff) {
			for (size_t j = 0; j < 8; j++) {
				if (!(bitmap[i] & (1 << j))) {
					bitmap[i] |= (1 << j);
					return i * 8 + j;
				}
			}
		}
	}
	return -1;
}

struct ipv4db_item_t *find_ip(struct pool_t *pool, int idx) {
	struct range_t *r = pool->range;
	int pos = 0;
	while (r) {
		if (pos + r->count > idx) {
			struct ipv4db_item_t *it = malloc(sizeof(struct ipv4db_item_t));
			it->owner = &ipdb;
			it->addr = r->start + idx - pos;
			it->mask = 32;
			it->peer_addr = r->gw;
			// store it in allocated_its
			pool->allocated_its[idx] = it;
			return it;
		}
		pos += r->count;
		r = r->next;
	}
	return NULL;
}

static struct ipv4db_item_t *get_ip(struct ap_session *ses) {
	char *pool_name = ses->ipv4_pool_name;
	struct pool_t *pool = NULL;

	if (pool_name) {
		for (size_t i = 0; i < pools_count; i++) {
			if (strcmp(pool_name, pools[i].name) == 0) {
				pool = &pools[i];
				break;
			}
		}
	} else {
		pool = &pools[0];
	}
	if (!pool) {
		return NULL;
	}

	int idx = find_free_bit(pool->bitmap, pool->bitmap_size);
	if (idx == -1) {
		log_warn("ippool: pool '%s' is empty or not defined\n", pool->name);
		return NULL;
	}

	return find_ip(pool, idx);
}

static void put_ip(struct ap_session *ses, struct ipv4db_item_t *it) {
	struct pool_t *pool = NULL;
	// find pool by name
	for (size_t i = 0; i < pools_count; i++) {
		if (strcmp(ses->ipv4_pool_name, pools[i].name) == 0) {
			pool = &pools[i];
			break;
		}
	}
	if (!pool) {
		pool = &pools[0];
	}
	// find it in allocated_its, to find bitmap index
	int idx = -1;
	for (size_t i = 0; i < pool->bitmap_size; i++) {
		if (pool->allocated_its[i] == it) {
			idx = i;
			break;
		}
	}
	if (idx == -1) {
		log_emerg("ippool: pointer not found on ip release, bug?\n");
		return;
	}
	// clear bitmap
	pool->bitmap[idx / 8] &= ~(1 << (idx % 8));
	// free it
	free(it);
}

static void poolng_init1(void)
{
	ipdb_register(&ipdb);
}


/*
pool4=net=subnet,size=ipcount[,gw=ip][,name=poolname]
Examples:
pool4=net=1.2.3.0,size=10
Means that pool with 10 addresses starting from 1.2.3.0 to 1.2.3.9 will be available for users.

pool4=net=1.2.1.0,size=255
pool4=net=1.2.10.0,size=255

This means for user available 510 addresses starting from 1.2.1.0 to 1.2.3.254 then 1.2.10.0 to 1.2.10.254

*/

struct poolparam_t {
	in_addr_t net;
	uint32_t size;
	in_addr_t gw;
	char name[64];
};

static struct poolparam_t *parse_subparam(const char *str) {
	struct poolparam_t *param = malloc(sizeof(struct poolparam_t));
	regex_t re;
	regmatch_t match[7];
	int rc;

	// sanity checks for str
	if (strlen(str) == 0 || strlen(str) > 255) {
		log_emerg("poolng: pool definition is too long\n");
		return NULL;
	}

	rc = regcomp(&re, "net=([0-9.]+),size=([0-9]+)(,gw=([0-9.]+))?(,name=([a-zA-Z0-9]+))?", REG_EXTENDED);
	if (rc != 0) {
		log_emerg("poolng: regcomp failed\n");
		return NULL;
	}

	rc = regexec(&re, str, 7, match, 0);
	if (rc != 0) {
		log_emerg("poolng: regexec failed\n");
		return NULL;
	}

	if (match[1].rm_so == -1 || match[2].rm_so == -1) {
		log_emerg("poolng: mandatory parameters net and size are missing or invalid\n");
		return NULL;
	}

	// parse parameters net and size
	param->net = inet_addr(str + match[1].rm_so);
	param->size = atoi(str + match[2].rm_so);
	// verify size
	if (param->size < 1) {
		log_emerg("poolng: invalid size\n");
		return NULL;
	}

	// gateway is optional
	if (match[4].rm_so != -1) {
		param->gw = inet_addr(str + match[4].rm_so);
	} else {
		param->gw = 0;
	}

	// pool name is optional, set to "default" if not specified
	if (match[6].rm_so != -1) {
		size_t len = match[6].rm_eo - match[6].rm_so;
		if (len > sizeof(param->name) - 1 || len == 0) {
			log_emerg("poolng: pool name is too long or empty\n");
			return NULL;
		}
		strncpy(param->name, str + match[6].rm_so, match[6].rm_eo - match[6].rm_so);
	} else {
		// set to "default" if not specified
		strcpy(param->name, "default");
	}

	return param;
}

#ifdef RADIUS
static int parse_attr(struct ap_session *ses, struct rad_attr_t *attr)
{
	if (conf_vendor == 9) {
		/* VENDOR_Cisco */
		if (attr->len > sizeof("ip:addr-pool=") && memcmp(attr->val.string, "ip:addr-pool=", sizeof("ip:addr-pool=") - 1) == 0) {
			if (ses->ipv4_pool_name)
				_free(ses->ipv4_pool_name);
			ses->ipv4_pool_name = _strdup(attr->val.string + sizeof("ip:addr-pool=") - 1);
		}
	} else {
		if (ses->ipv4_pool_name)
			_free(ses->ipv4_pool_name);

		ses->ipv4_pool_name = _strdup(attr->val.string);
	}

	return 0;
}

static void ev_radius_access_accept(struct ev_radius_t *ev)
{
	struct rad_attr_t *attr;

	list_for_each_entry(attr, &ev->reply->attrs, entry) {
		if (attr->attr->type != ATTR_TYPE_STRING)
			continue;
		if (attr->vendor && attr->vendor->id != conf_vendor)
			continue;
		if (!attr->vendor && conf_vendor)
			continue;
		if (attr->attr->id != conf_attr)
			continue;
		parse_attr(ev->ses, attr);
	}
}

static int parse_attr_opt(const char *opt)
{
	struct rad_dict_attr_t *attr;
	struct rad_dict_vendor_t *vendor;

	if (conf_vendor)
		vendor = rad_dict_find_vendor_id(conf_vendor);
	else
		vendor = NULL;

	if (conf_vendor) {
		if (vendor)
			attr = rad_dict_find_vendor_attr(vendor, opt);
		else
			attr = NULL;
	}else
		attr = rad_dict_find_attr(opt);

	if (attr)
		return attr->id;

	return atoi(opt);
}

static int parse_vendor_opt(const char *opt)
{
	struct rad_dict_vendor_t *vendor;

	vendor = rad_dict_find_vendor_name(opt);
	if (vendor)
		return vendor->id;

	return atoi(opt);
}
#endif


static void allocate_pool(const char *cfgline) {
	struct poolparam_t *param = parse_subparam(cfgline);
	struct pool_t *pool = NULL;

	if (!param) {
		log_emerg("poolng: invalid pool definition\n");
		free(param);
		return;
	}

	// define range
	struct range_t *range = malloc(sizeof(struct range_t));
	range->start = param->net;
	range->count = param->size;
	range->gw = param->gw;
	range->next = NULL;


	if (!pools) {
		log_debug("poolng: creating first pool: %s\n", param->name);
		pools = malloc(sizeof(struct pool_t));
		pools_count = 1;
		pool = &pools[0];
		pool->range = range;
		pool->bitmap = malloc(param->size);
		pool->bitmap_size = param->size;
		memset(pool->bitmap, 0, param->size);
		// allocate memory for allocated_its
		pool->allocated_its = malloc(sizeof(struct ipv4db_item_t*) * param->size);
	} else {
		/* Search in pools same name, as one pool might be defined multiple times with different subnets */
		for (size_t i = 0; i < pools_count; i++) {
			if (strcmp(param->name, pools[i].name) == 0) {
				pool = &pools[i];
				break;
			}
		}
		// if no pool with this name exists, create new one to pool of pools
		if (!pool) {			
			log_debug("poolng: creating new pool: %s\n", param->name);
			pools = realloc(pools, sizeof(struct pool_t) * (pools_count + 1));
			pool = &pools[pools_count];
			pools_count++;
			pool->range = range;
			pool->bitmap = malloc(param->size);
			pool->bitmap_size = param->size;
			memset(pool->bitmap, 0, param->size);
			// allocate memory for allocated_its
			pool->allocated_its = malloc(sizeof(struct ipv4db_item_t*) * param->size);
		} else {
			log_debug("poolng: extending pool: %s\n", param->name);
			// if pool with this name exists, add new range to it and extend bitmap
			struct range_t *r = pool->range;
			// pool already exists, extend old bitmap and add new range over next
			pool->bitmap = realloc(pool->bitmap, pool->bitmap_size + param->size);
			pool->bitmap_size += param->size;
			memset(pool->bitmap + pool->bitmap_size - param->size, 0, param->size);
			while (r->next) {
				r = r->next;
			}
			r->next = range;		
			// realloc allocated_its
			pool->allocated_its = realloc(pool->allocated_its, sizeof(struct ipv4db_item_t*) * pool->bitmap_size);
			free(param);
			return;
		}
	}
	free(param);
}

static void poolng_init2(void)
{
	struct conf_sect_t *s = conf_get_section("poolng");
	struct conf_option_t *opt;

	if (!s) {
		log_emerg("poolng: section 'poolng' is not defined\n");
		return;
	}

	list_for_each_entry(opt, &s->items, entry) {
#ifdef RADIUS
		if (triton_module_loaded("radius")) {
			if (!strcmp(opt->name, "vendor")) {
				conf_vendor = parse_vendor_opt(opt->val);
				continue;
			} else if (!strcmp(opt->name, "attr")) {
				conf_attr = parse_attr_opt(opt->val);
				continue;
			}
		}
#endif
		if (strcmp(opt->name, "pool4") == 0) {
			allocate_pool(opt->val);
		}
	}

#ifdef RADIUS
	if (triton_module_loaded("radius"))
		triton_event_register_handler(EV_RADIUS_ACCESS_ACCEPT, (triton_event_func)ev_radius_access_accept);
#endif
}

static struct ipdb_t ipdb = {
	.get_ipv4 = get_ip,
	.put_ipv4 = put_ip,
};

DEFINE_INIT(51, poolng_init1);
DEFINE_INIT2(52, poolng_init2);
