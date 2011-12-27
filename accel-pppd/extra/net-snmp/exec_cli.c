/*
 * Note: this file originally auto-generated by mib2c using
 *        : mib2c.scalar.conf 11805 2005-01-07 09:37:18Z dts12 $
 */

#include <net-snmp/net-snmp-config.h>
#include <net-snmp/net-snmp-includes.h>
#include <net-snmp/agent/net-snmp-agent-includes.h>
#include "exec_cli.h"
#include "cli_p.h"

#include "memdebug.h"

static void no_disconnect(struct cli_client_t *tcln)
{
}

static int no_send(struct cli_client_t *tcln, const void *_buf, int size)
{
	return 0;
}

static int no_sendv(struct cli_client_t *tcln, const char *fmt, va_list ap)
{
	return 0;
}

static void set_action(const char *cmd, size_t len)
{
	struct cli_client_t cc = {
		.cmdline = _malloc(len + 1),
		.send = no_send,
		.sendv = no_sendv,
		.disconnect = no_disconnect,
	};

	memcpy(cc.cmdline, cmd, len);
	cc.cmdline[len] = 0;
	
	cli_process_cmd(&cc);

	_free(cc.cmdline);
}

/** Initializes the cli module */
void
init_cli(void)
{
    static oid cli_oid[] = { 1,3,6,1,4,1,8072,100,3,3 };

  DEBUGMSGTL(("cli", "Initializing\n"));

    netsnmp_register_scalar(
        netsnmp_create_handler_registration("cli", handle_cli,
                               cli_oid, OID_LENGTH(cli_oid),
                               HANDLER_CAN_RWRITE
        ));
}

int
handle_cli(netsnmp_mib_handler *handler,
                          netsnmp_handler_registration *reginfo,
                          netsnmp_agent_request_info   *reqinfo,
                          netsnmp_request_info         *requests)
{
    int ret;
    /* We are never called for a GETNEXT if it's registered as a
       "instance", as it's "magically" handled for us.  */

    /* a instance handler also only hands us one request at a time, so
       we don't need to loop over a list of requests; we'll only get one. */
    
    switch(reqinfo->mode) {

        case MODE_GET:
            netsnmp_set_request_error(reqinfo, requests, SNMP_NOSUCHINSTANCE );
            break;

        /*
         * SET REQUEST
         *
         * multiple states in the transaction.  See:
         * http://www.net-snmp.org/tutorial-5/toolkit/mib_module/set-actions.jpg
         */
        case MODE_SET_RESERVE1:
                /* or you could use netsnmp_check_vb_type_and_size instead */
            ret = netsnmp_check_vb_type(requests->requestvb, ASN_OCTET_STR);
            if ( ret != SNMP_ERR_NOERROR ) {
                netsnmp_set_request_error(reqinfo, requests, ret );
            }
            break;

        case MODE_SET_RESERVE2:
            /* XXX malloc "undo" storage buffer */
            break;

        case MODE_SET_FREE:
            /* XXX: free resources allocated in RESERVE1 and/or
               RESERVE2.  Something failed somewhere, and the states
               below won't be called. */
            break;

        case MODE_SET_ACTION:
            /* XXX: perform the value change here */
						set_action((char *)requests->requestvb->val.string, requests->requestvb->val_len);
            break;

        case MODE_SET_COMMIT:
            /* XXX: delete temporary storage */
            break;

        case MODE_SET_UNDO:
            /* XXX: UNDO and return to previous value for the object */
            break;

        default:
            /* we should never get here, so this is a really bad error */
            snmp_log(LOG_ERR, "unknown mode (%d) in handle_cli\n", reqinfo->mode );
            return SNMP_ERR_GENERR;
    }

    return SNMP_ERR_NOERROR;
}
