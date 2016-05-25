/*
 * Softmodem for Asterisk
 *
 * 2010, Christian Groeger <code@proquari.at>
 * 
 * Based on app_fax.c by Dmitry Andrianov <asterisk@dima.spb.ru>
 * and Steve Underwood <steveu@coppice.org>
 *
 * This program is free software, distributed under the terms of
 * the GNU General Public License
 *
 */

/*** MODULEINFO
	 <depend>spandsp</depend>
	<support_level>extended</support_level>
***/
 
#include "asterisk.h"

ASTERISK_FILE_VERSION(__FILE__, "$Revision$")

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <inttypes.h>
#include <pthread.h>
#include <errno.h>
#include <tiffio.h>
#include <time.h>

#include <spandsp.h>
#ifdef HAVE_SPANDSP_EXPOSE_H
#include <spandsp/expose.h>
#endif
#include <spandsp/v22bis.h>

#include "asterisk/file.h"
#include "asterisk/module.h"
#include "asterisk/channel.h"
#include "asterisk/strings.h"
#include "asterisk/lock.h"
#include "asterisk/app.h"
#include "asterisk/pbx.h"
#include "asterisk/format_cache.h"
#include "asterisk/logger.h"
#include "asterisk/utils.h"
#include "asterisk/dsp.h"
#include "asterisk/manager.h"

#ifndef AST_MODULE
#define AST_MODULE "app_softmodem"
#endif

/*** DOCUMENTATION
	<application name="Softmodem" language="en_US">
		<synopsis>
			A Softmodem that connects the caller to a Telnet server.
		</synopsis>
		<syntax />
		<description>
			<para>Softmodem(hostname,port,options):  Simulates a FSK(V.23) or V.22bis modem. The modem on the other end is connected to the specified server using a simple TCP connection (like Telnet).</para>
		</description>
	</application>
 ***/

/**
 * 	"Options:"
	"  r(...): rx cutoff (dBi, float, default: -35)\n"
	"  t(...): tx power (dBi, float, default: -28)\n"
	"  v(...): modem version (default: V23):\n"
	"            V21        - 300/300 baud\n"
	"            V23        - 1200/75 baud\n"
	"            Bell103    - 300/300 baud\n"
	"            V22        - 1200/1200 baud\n"
	"            V22bis     - 2400/2400 baud\n"
	"  l or m: least or most significant bit first (default: m)\n"
	"  d(...): amount of data bits (5-8, default: 8)\n"
	"  s(...): amount of stop bits (1-2, default: 1)\n"
	"  u:      Send ULM header to Telnet server (Btx)\n"
	"  n:      Send NULL-Byte to modem after carrier detection (Btx)\n" **/

static const char app[] = "Softmodem";

enum {
	OPT_RX_CUTOFF =      (1 << 0),
	OPT_TX_POWER =       (1 << 1),
	OPT_MODEM_VERSION =  (1 << 2),
	OPT_LSB_FIRST =      (1 << 3),
	OPT_MSB_FIRST =      (1 << 4),
	OPT_DATABITS =       (1 << 5),
	OPT_STOPBITS =       (1 << 6),
	OPT_ULM_HEADER =     (1 << 7),
	OPT_NULL =           (1 << 8),
};

enum {
	OPT_ARG_RX_CUTOFF,
	OPT_ARG_TX_POWER,
	OPT_ARG_MODEM_VERSION,
	OPT_ARG_DATABITS,
	OPT_ARG_STOPBITS,

	/* Must be the last element */
	OPT_ARG_ARRAY_SIZE,
};

AST_APP_OPTIONS(additional_options, BEGIN_OPTIONS
	AST_APP_OPTION_ARG('r', OPT_RX_CUTOFF, OPT_ARG_RX_CUTOFF),
	AST_APP_OPTION_ARG('t', OPT_TX_POWER, OPT_ARG_TX_POWER),
	AST_APP_OPTION_ARG('v', OPT_MODEM_VERSION, OPT_ARG_MODEM_VERSION),
	AST_APP_OPTION('l', OPT_LSB_FIRST),
	AST_APP_OPTION('m', OPT_MSB_FIRST),
	AST_APP_OPTION_ARG('d', OPT_DATABITS, OPT_ARG_DATABITS),
	AST_APP_OPTION_ARG('s', OPT_STOPBITS, OPT_ARG_STOPBITS),
	AST_APP_OPTION('u', OPT_ULM_HEADER),
	AST_APP_OPTION('n', OPT_NULL),
END_OPTIONS );


#define MAX_SAMPLES 240

enum {
	VERSION_V21,
	VERSION_V23,
	VERSION_BELL103,
	VERSION_V22,
	VERSION_V22BIS,
};

typedef struct {
	struct ast_channel *chan;
	const char *host;	//telnetd host+port
	int port;
	float txpower;
	float rxcutoff;
	int version;
	int lsb;
	int databits;
	int stopbits;
	int ulmheader;
	int sendnull;
	volatile int finished;
} modem_session;

#define MODEM_BITBUFFER_SIZE 16
typedef struct {
	int answertone;		// terminal is active (=sends data)
	int nulsent;		// we sent a NULL as very first character (at least the DBT03 expects this)
} connection_state;
typedef struct {
	int sock;
	int bitbuffer[MODEM_BITBUFFER_SIZE];
	int writepos;
	int readpos;
	int fill;
	connection_state *state;
	modem_session *session;
} modem_data;


// this is called by spandsp whenever it filtered a new bit from the line
static void modem_put_bit(void *user_data, int bit) {
	int stop, stop2, i;
	
	modem_data *rx = (modem_data*) user_data;
	
	int databits = rx->session->databits;
	int stopbits = rx->session->stopbits;
	
	// modem recognised us and starts responding through sending it's pilot signal
	if (rx->state->answertone<=0) {
		if (bit==SIG_STATUS_CARRIER_UP) {
			rx->state->answertone=0;
		}
		else if (bit==1 && rx->state->answertone==0) {
			rx->state->answertone=1;
		}
	}
	else {
		// ignore other spandsp-stuff
		if (bit==1 || bit==0) {
			
			// insert bit into our bitbuffer
			rx->bitbuffer[rx->writepos]=bit;
			rx->writepos++;
			if (rx->writepos>=MODEM_BITBUFFER_SIZE) rx->writepos=0;
			
			if (rx->fill<MODEM_BITBUFFER_SIZE) {
				rx->fill++;
			} else { 
				// our bitbuffer is full, this probably won't happen
	// 			printf("full buffer\n");
				rx->readpos++;
				if (rx->readpos>=MODEM_BITBUFFER_SIZE) rx->readpos=0;
			}
			
			// full byte = 1 startbit + databits + stopbits
			while (rx->fill>=(1+databits+stopbits)) {
				if (rx->bitbuffer[rx->readpos]==0) {	// check for startbit
					stop=(rx->readpos+1+databits)%MODEM_BITBUFFER_SIZE;
					stop2=(rx->readpos+2+databits)%MODEM_BITBUFFER_SIZE;
					if ( (rx->bitbuffer[stop]==1) &&
						(stopbits==1 || (stopbits==2 && rx->bitbuffer[stop2]==1)) )
					{	// check for stopbit -> valid framing
						char byte=0;
						
						for(i=0; i<databits; i++) {	// generate byte
							if (rx->session->lsb) { //lsb first
								if (rx->bitbuffer[(rx->readpos+1+i)%MODEM_BITBUFFER_SIZE])
									byte |= (1<<i);
							} else { //msb first
								if (rx->bitbuffer[(rx->readpos+databits-i)%MODEM_BITBUFFER_SIZE])
									byte |= (1<<i);
							}
						}
						
						send(rx->sock, &byte, 1, 0);
						
						rx->readpos=(rx->readpos+10)%MODEM_BITBUFFER_SIZE;
						rx->fill-=10;
						
					} else {	// no valid framing (no stopbit), remove first bit and maybe try again
						rx->fill--;
						rx->readpos++;
						rx->readpos %= MODEM_BITBUFFER_SIZE;
					}
				} else {	// no valid framing either (no startbit)
					rx->fill--;
					rx->readpos++;
					rx->readpos %= MODEM_BITBUFFER_SIZE;
				}
			}
		}
	}
	
	
	
	return;
}

// spandsp asks us for a bit to send onto the line
static int modem_get_bit(void *user_data) {
	modem_data *tx = (modem_data*) user_data;
	char byte=0;
	int i, rc;
	
	int databits=tx->session->databits;
	int stopbits=tx->session->stopbits;
	
	// no new data in send (bit)buffer, 
	// either we just picked up the line, the terminal started to respond,
	// than we check for new data on the socket
	// or there's no new data, so we send 1s (mark)
	if (tx->writepos==tx->readpos) {
		if(tx->state->nulsent>0) {	// connection is established, look for data on socket
			rc=recv(tx->sock,&byte, 1, 0);
			if (rc>0) {
				// new data on socket, we put that byte into our bitbuffer
				for (i=0; i<(databits+stopbits); i++) {
					if (i>=databits) tx->bitbuffer[tx->writepos]=1;	// stopbits
					else {	// databits
						if (tx->session->lsb) {
							if (byte & (1<<i)) tx->bitbuffer[tx->writepos]=1;
							else tx->bitbuffer[tx->writepos]=0;
						} else {
							if (byte & (1<<(databits-1-i))) tx->bitbuffer[tx->writepos]=1;
							else tx->bitbuffer[tx->writepos]=0;
						}
					}
					tx->writepos++;
					if (tx->writepos>=MODEM_BITBUFFER_SIZE) tx->writepos=0;
				}
				return 0; // return startbit immediately
			}
			else if (rc==0) {
				ast_log(LOG_WARNING,"Socket seems closed. Will hangup.\n");
				tx->session->finished=1;
			}
		}
		else {
			// check if socket was closed before connection was terminated
			if ( recv(tx->sock,&byte, 1, MSG_PEEK) == 0 ) {
				tx->session->finished=1;
				return 1;
			}
			if ( tx->state->answertone>0 ) {
// 				ast_log(LOG_WARNING,"Got TE's tone, will send null-byte.\n");
				
				if (tx->session->sendnull) { // send null byte
					for (i=0; i<(databits+stopbits); i++) {
						if (i>=databits) tx->bitbuffer[tx->writepos]=1;	//stopbits
						else tx->bitbuffer[tx->writepos]=0; //databits
						tx->writepos++;
						if (tx->writepos>=MODEM_BITBUFFER_SIZE) tx->writepos=0;
					}
				}
				tx->state->nulsent=1;
				
				if (tx->session->ulmheader) {
					// send ULM relay protocol header, include connection speed
					float tx_baud,rx_baud;
					if (tx->session->version==VERSION_V21) {
						tx_baud=300;
						rx_baud=300;
					} else if (tx->session->version==VERSION_V23) {
						tx_baud=1200;
						rx_baud=75;
					} else if (tx->session->version==VERSION_BELL103) {
						tx_baud=300;
						rx_baud=300;
					} else if (tx->session->version==VERSION_V22) {
						tx_baud=1200;
						rx_baud=1200;
					} else if (tx->session->version==VERSION_V22BIS) {
						tx_baud=2400;
						rx_baud=2400;
					} else {
						tx_baud=0;
						rx_baud=0;
					}
					
					char header[60];
					int headerlength=sprintf(header, 
						"Version: 1\r\nTXspeed: %.2f\r\nRXspeed: %.2f\r\n\r\n",
						tx_baud/(1+databits+stopbits), rx_baud/(1+databits+stopbits));
					send(tx->sock, header, headerlength, 0);
				}
				
				if (tx->session->sendnull)
					return 0;
				else
					return 1;
			}
		}
		
		// no new data on socket, NULL-byte already sent, send mark-frequency 
		return 1;
		
	} else {
		// there still is data in the bitbuffer, so we just send that out
		i=tx->bitbuffer[tx->readpos];
		tx->readpos++;
		if (tx->readpos>=MODEM_BITBUFFER_SIZE) tx->readpos=0;
// 		printf("b%i",i);
		return i;
	}
}

static void *modem_generator_alloc(struct ast_channel *chan, void *params)
{
	return params;
}

static int fsk_generator_generate(struct ast_channel *chan, void *data, int len, int samples)
{
	fsk_tx_state_t *tx = (fsk_tx_state_t*) data;
	uint8_t buffer[AST_FRIENDLY_OFFSET + MAX_SAMPLES * sizeof(uint16_t)];
	int16_t *buf = (int16_t *) (buffer + AST_FRIENDLY_OFFSET);
	
	struct ast_frame outf = {
		.frametype = AST_FRAME_VOICE,
		.subclass.format = ast_format_slin,
		.src = __FUNCTION__,
	};

	if (samples > MAX_SAMPLES) {
		ast_log(LOG_WARNING, "Only generating %d samples, where %d requested\n", MAX_SAMPLES, samples);
		samples = MAX_SAMPLES;
	}

	
	if ((len = fsk_tx(tx, buf, samples)) > 0) {
		outf.samples = len;
		AST_FRAME_SET_BUFFER(&outf, buffer, AST_FRIENDLY_OFFSET, len * sizeof(int16_t));

		if (ast_write(chan, &outf) < 0) {
			ast_log(LOG_WARNING, "Failed to write frame to %s: %s\n", ast_channel_name(chan), strerror(errno));
			return -1;
		}
	}

	return 0;
}


static int v22_generator_generate(struct ast_channel *chan, void *data, int len, int samples)
{
	v22bis_state_t *tx = (v22bis_state_t*) data;
	uint8_t buffer[AST_FRIENDLY_OFFSET + MAX_SAMPLES * sizeof(uint16_t)];
	int16_t *buf = (int16_t *) (buffer + AST_FRIENDLY_OFFSET);
	
	struct ast_frame outf = {
		.frametype = AST_FRAME_VOICE,
		.subclass.format = ast_format_slin,
		.src = __FUNCTION__,
	};

	if (samples > MAX_SAMPLES) {
		ast_log(LOG_WARNING, "Only generating %d samples, where %d requested\n", MAX_SAMPLES, samples);
		samples = MAX_SAMPLES;
	}

	
	if ((len = v22bis_tx(tx, buf, samples)) > 0) {
		outf.samples = len;
		AST_FRAME_SET_BUFFER(&outf, buffer, AST_FRIENDLY_OFFSET, len * sizeof(int16_t));

		if (ast_write(chan, &outf) < 0) {
			ast_log(LOG_WARNING, "Failed to write frame to %s: %s\n", ast_channel_name(chan), strerror(errno));
			return -1;
		}
	}

	return 0;
}

struct ast_generator fsk_generator = {
	alloc:		modem_generator_alloc,
	generate: 	fsk_generator_generate,
};
struct ast_generator v22_generator = {
	alloc:		modem_generator_alloc,
	generate: 	v22_generator_generate,
};

static int softmodem_communicate(modem_session *s) {
	int res = -1;
	struct ast_format *original_read_fmt;
	struct ast_format *original_write_fmt;
	
	modem_data rxdata, txdata;
	
	struct ast_frame *inf = NULL;
	
	fsk_tx_state_t *modem_tx;
	fsk_rx_state_t *modem_rx;
	
	v22bis_state_t *v22_modem;
	
	
	original_read_fmt = ast_channel_readformat(s->chan);
	if (original_read_fmt != ast_format_slin) {
		res=ast_set_read_format(s->chan, ast_format_slin);
		if (res < 0) {
			ast_log(LOG_WARNING, "Unable to set to linear read mode, giving up\n");
			return res;
		}
	}

	original_write_fmt = ast_channel_writeformat(s->chan);
	if (original_write_fmt != ast_format_slin) {
		res=ast_set_write_format(s->chan, ast_format_slin);
		if (res < 0) {
			ast_log(LOG_WARNING, "Unable to set to linear write mode, giving up\n");
			return res;
		}
	}
	
	int sock;
	struct sockaddr_in server;
	struct hostent *hp;
	struct ast_hostent ahp;
	
	sock = socket(AF_INET, SOCK_STREAM, 0);
	if(sock < 0) {
		ast_log(LOG_WARNING, "Could not create socket.\n");
		return res;
	}
	
	server.sin_family=AF_INET;
	hp=ast_gethostbyname(s->host, &ahp);
	memcpy( (char *)&server.sin_addr, hp->h_addr, hp->h_length);
	//bcopy ( hp->h_addr, &(server.sin_addr.s_addr), hp->h_length);
	server.sin_port=htons(s->port);
	
	if (connect(sock, (struct sockaddr*)&server, sizeof(server)) < 0) {
		ast_log(LOG_WARNING, "Cannot connect to remote host.\n");
		return res;
	}
	
	fcntl(sock, F_SETFL, O_NONBLOCK);
	
	
	connection_state state;
	state.answertone=-1;	//no carrier yet
	state.nulsent=0;
	
	rxdata.sock=sock;
	rxdata.writepos=0;
	rxdata.readpos=0;
	rxdata.fill=0;
	rxdata.state= &state;
	rxdata.session=s;
	
	txdata.sock=sock;
	txdata.writepos=0;
	txdata.readpos=0;
	txdata.fill=0;
	txdata.state= &state;
	txdata.session=s;
	
	// initialise spandsp-stuff, give it our callback-functions
	if (s->version==VERSION_V21) {
		modem_tx = fsk_tx_init(NULL, &preset_fsk_specs[FSK_V21CH2], modem_get_bit, &txdata);
		modem_rx = fsk_rx_init(NULL, &preset_fsk_specs[FSK_V21CH1], TRUE, modem_put_bit, &rxdata);
	}
	else if (s->version==VERSION_V23) {
		modem_tx = fsk_tx_init(NULL, &preset_fsk_specs[FSK_V23CH1], modem_get_bit, &txdata);
		modem_rx = fsk_rx_init(NULL, &preset_fsk_specs[FSK_V23CH2], TRUE, modem_put_bit, &rxdata);
	}
	else if (s->version==VERSION_BELL103) {
		modem_tx = fsk_tx_init(NULL, &preset_fsk_specs[FSK_BELL103CH1], modem_get_bit, &txdata);
		modem_rx = fsk_rx_init(NULL, &preset_fsk_specs[FSK_BELL103CH2], TRUE, modem_put_bit, &rxdata);
	}
	else if (s->version==VERSION_V22) {
		v22_modem = v22bis_init(NULL, 1200, 0, FALSE, modem_get_bit, &txdata, modem_put_bit, &rxdata);
	}
	else if (s->version==VERSION_V22BIS) {
		v22_modem = v22bis_init(NULL, 2400, 0, FALSE, modem_get_bit, &txdata, modem_put_bit, &rxdata);
	}
	else {
		ast_log(LOG_ERROR,"Unsupported modem type. Sorry.\n");
		return res;
	}
	
	if (s->version==VERSION_V21 || s->version==VERSION_V23 || s->version==VERSION_BELL103) {
		fsk_tx_power (modem_tx, s->txpower);
		fsk_rx_signal_cutoff(modem_rx, s->rxcutoff);
	}
	else if (s->version==VERSION_V22 || s->version==VERSION_V22BIS) {
		v22bis_tx_power(v22_modem, s->txpower);
		v22bis_rx_signal_cutoff(v22_modem, s->rxcutoff);
	}
	
	//printf("comm: baud %i\n",btx_tx->baud_rate);
	if (s->version==VERSION_V21 || s->version==VERSION_V23 || s->version==VERSION_BELL103)
		ast_activate_generator(s->chan, &fsk_generator, modem_tx);
	else if (s->version==VERSION_V22 || s->version==VERSION_V22BIS)
		ast_activate_generator(s->chan, &v22_generator, v22_modem);
	
	while (!s->finished) {
		res = ast_waitfor(s->chan, 20);
		if (res < 0)
			break;
		else if (res > 0)
			res = 0;

		inf = ast_read(s->chan);
		if (inf == NULL) {
			ast_debug(1, "Channel hangup\n");
			res = -1;
			break;
		}
		
		/* Check the frame type. Format also must be checked because there is a chance
		   that a frame in old format was already queued before we set chanel format
		   to slinear so it will still be received by ast_read */
		if (inf->frametype == AST_FRAME_VOICE && inf->subclass.format == ast_format_slin) {
			if (s->version==VERSION_V21 || s->version==VERSION_V23 || s->version==VERSION_BELL103) {
				if (fsk_rx(modem_rx, inf->data.ptr, inf->samples) < 0) {
					/* I know fax_rx never returns errors. The check here is for good style only */
					ast_log(LOG_WARNING, "softmodem returned error\n");
					res = -1;
					break;
				}
			}
			else if (s->version==VERSION_V22 || s->version==VERSION_V22BIS) {
				if (v22bis_rx(v22_modem, inf->data.ptr, inf->samples) < 0) {
					ast_log(LOG_WARNING, "softmodem returned error\n");
					res = -1;
					break;
				}
			}
		}
		
		ast_frfree(inf);
		inf = NULL;
	}
	
	close(sock);
	
	if (s->version==VERSION_V22 || s->version==VERSION_V22BIS) {
		v22bis_release(v22_modem);
		v22bis_free(v22_modem);
	}
	
	if (original_write_fmt != ast_format_slin) {
		if (ast_set_write_format(s->chan, original_write_fmt) < 0)
			ast_log(LOG_WARNING, "Unable to restore write format on '%s'\n", ast_channel_name(s->chan));
	}

	if (original_read_fmt != ast_format_slin) {
		if (ast_set_read_format(s->chan, original_read_fmt) < 0)
			ast_log(LOG_WARNING, "Unable to restore read format on '%s'\n", ast_channel_name(s->chan));
	}

	return res;

}

static int softmodem_exec(struct ast_channel *chan, const char *data) {
	int res = 0;
	char *parse;
	modem_session session;
	struct ast_flags options = { 0, };
	char *option_args[OPT_ARG_ARRAY_SIZE];

	AST_DECLARE_APP_ARGS(args,
		AST_APP_ARG(host);
		AST_APP_ARG(port);
		AST_APP_ARG(options);
	);

	if (chan == NULL) {
		ast_log(LOG_ERROR, "Channel is NULL. Giving up.\n");
		return -1;
	}
	
	/* answer channel if not already answered */
	if (ast_channel_state(chan) != AST_STATE_UP) {
		res = ast_answer(chan);
		if (res) {
			ast_log(LOG_WARNING, "Could not answer channel '%s'\n", ast_channel_name(chan));
			return res;
		}
	}
	
	session.chan=chan;
	session.finished=0;
	session.rxcutoff=-35.0f;
	session.txpower=-28.0f;
	session.version=VERSION_V23;
	session.lsb=0;
	session.databits=8;
	session.stopbits=1;
	session.ulmheader=0;
	session.sendnull=0;
	
	parse=ast_strdupa(data);
	AST_STANDARD_APP_ARGS(args,parse);
	
	if (args.host)
		session.host=args.host;
	else
		session.host="localhost";
	
	if (args.port) {
		session.port=atoi(args.port);
		if ((session.port<0) || (session.port>65535)) {
			ast_log(LOG_ERROR, "Please specify a valid port number.\n");
			return -1;
		}
	} else
		session.port=23;
	
	
	if (args.options) {
		ast_app_parse_options(additional_options, &options, option_args, args.options);
		
		if (ast_test_flag(&options, OPT_RX_CUTOFF)) {
			if (!ast_strlen_zero(option_args[OPT_ARG_RX_CUTOFF]))
				session.rxcutoff=atof(option_args[OPT_ARG_RX_CUTOFF]);
		}
		
		if (ast_test_flag(&options, OPT_TX_POWER)) {
			if (!ast_strlen_zero(option_args[OPT_ARG_TX_POWER]))
				session.txpower=atof(option_args[OPT_ARG_TX_POWER]);
		}
		
		if (ast_test_flag(&options, OPT_MODEM_VERSION)) {
			if (!ast_strlen_zero(option_args[OPT_ARG_MODEM_VERSION])) {
				if (strcmp(option_args[OPT_ARG_MODEM_VERSION],"V21")==0)
					session.version=VERSION_V21;
				else if (strcmp(option_args[OPT_ARG_MODEM_VERSION],"V23")==0)
					session.version=VERSION_V23;
				else if (strcmp(option_args[OPT_ARG_MODEM_VERSION],"Bell103")==0)
					session.version=VERSION_BELL103;
				else if (strcmp(option_args[OPT_ARG_MODEM_VERSION],"V22")==0)
					session.version=VERSION_V22;
				else if (strcmp(option_args[OPT_ARG_MODEM_VERSION],"V22bis")==0)
					session.version=VERSION_V22BIS;
			}
		}
		
		if (ast_test_flag(&options, OPT_LSB_FIRST)) {
			if (ast_test_flag(&options, OPT_MSB_FIRST)) {
				ast_log(LOG_ERROR, "Please only set l or m flag, not both.\n");
				return -1;
			}
			session.lsb=1;
		}
		
		if (ast_test_flag(&options, OPT_DATABITS)) {
			if (!ast_strlen_zero(option_args[OPT_ARG_DATABITS])) {
				session.databits = atoi(option_args[OPT_ARG_DATABITS]);
				
				if ((session.databits<5) || (session.databits>8)) {
					ast_log(LOG_ERROR, "Only 5-8 data bits are supported.\n");
					return -1;
				}
			}
		}
		
		if (ast_test_flag(&options, OPT_STOPBITS)) {
			if (!ast_strlen_zero(option_args[OPT_ARG_STOPBITS])) {
				session.stopbits = atoi(option_args[OPT_ARG_STOPBITS]);
				if ((session.stopbits<1) || (session.stopbits>2)) {
					ast_log(LOG_ERROR, "Only 1-2 stop bits are supported.\n");
					return -1;
				}
			}
		}
		
		if (ast_test_flag(&options, OPT_ULM_HEADER)) {
			session.ulmheader = 1;
		}
		if (ast_test_flag(&options, OPT_NULL)) {
			session.sendnull = 1;
		}
	}
	
	res=softmodem_communicate(&session);
	
	return res;
}



static int unload_module(void) {
	return ast_unregister_application(app);
}

static int load_module(void) {
	return ast_register_application_xml(app, softmodem_exec);
}


AST_MODULE_INFO_STANDARD_EXTENDED(ASTERISK_GPL_KEY, "Softmodem v22");