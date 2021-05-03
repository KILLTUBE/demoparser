#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <ctype.h>
#include <stdarg.h>
#include <string.h>
#include <stdint.h>
#include <unistd.h>

#include "declarations.hpp"

#define Com_Memset memset
#define Com_Printf printf
#define Com_DPrintf printf
#define Q_vsnprintf vsnprintf
#define Com_Memcpy memcpy
#define Com_Memset memset

#define ERR_FATAL 0
#define ERR_DROP 1
void Com_Error(int err, char* fmt,...)
{
	char buf[MAX_STRING_CHARS];

	va_list		argptr;

	va_start (argptr,fmt);
	Q_vsnprintf(buf, sizeof(buf), fmt, argptr);
	va_end (argptr);

	fputs(buf, stdout);
	exit(1);
}

static huffman_t msgHuff;
static qboolean	msgInit = qfalse;

int LittleLong( int l )
{
	return l;
}

// BEGIN huffman.c from Enemy Territory
static int bloc = 0;

//bani - optimized version
//clears data along the way so we dont have to memset() it ahead of time
void    Huff_putBit( int bit, byte *fout, int *offset )
{
	int x, y;
	bloc = *offset;
	x = bloc >> 3;
	y = bloc & 7;
	if ( !y )
	{
		fout[ x ] = 0;
	}
	fout[ x ] |= bit << y;
	bloc++;
	*offset = bloc;
}

//bani - optimized version
//optimization works on gcc 3.x, but not 2.95 ? most curious.
int Huff_getBit( byte *fin, int *offset )
{
	int t;
	bloc = *offset;
	t = fin[ bloc >> 3 ] >> ( bloc & 7 ) & 0x1;
	bloc++;
	*offset = bloc;
	return t;
}

//bani - optimized version
//clears data along the way so we dont have to memset() it ahead of time
static void add_bit( char bit, byte *fout )
{
	int x, y;

	y = bloc >> 3;
	x = bloc++ & 7;
	if ( !x )
	{
		fout[ y ] = 0;
	}
	fout[ y ] |= bit << x;
}

//bani - optimized version
//optimization works on gcc 3.x, but not 2.95 ? most curious.
static int get_bit( byte *fin )
{
	int t;
	t = fin[ bloc >> 3 ] >> ( bloc & 7 ) & 0x1;
	bloc++;
	return t;
}

static node_t **get_ppnode( huff_t* huff )
{
	node_t **tppnode;
	if ( !huff->freelist )
	{
		return &( huff->nodePtrs[huff->blocPtrs++] );
	}
	else
	{
		tppnode = huff->freelist;
		huff->freelist = (node_t **)*tppnode;
		return tppnode;
	}
}

static void free_ppnode( huff_t* huff, node_t **ppnode )
{
	*ppnode = (node_t *)huff->freelist;
	huff->freelist = ppnode;
}

/* Swap the location of these two nodes in the tree */
static void swap( huff_t* huff, node_t *node1, node_t *node2 )
{
	node_t *par1, *par2;

	par1 = node1->parent;
	par2 = node2->parent;

	if ( par1 )
	{
		if ( par1->left == node1 )
		{
			par1->left = node2;
		}
		else
		{
			par1->right = node2;
		}
	}
	else
	{
		huff->tree = node2;
	}

	if ( par2 )
	{
		if ( par2->left == node2 )
		{
			par2->left = node1;
		}
		else
		{
			par2->right = node1;
		}
	}
	else
	{
		huff->tree = node1;
	}

	node1->parent = par2;
	node2->parent = par1;
}

/* Swap these two nodes in the linked list (update ranks) */
static void swaplist( node_t *node1, node_t *node2 )
{
	node_t *par1;

	par1 = node1->next;
	node1->next = node2->next;
	node2->next = par1;

	par1 = node1->prev;
	node1->prev = node2->prev;
	node2->prev = par1;

	if ( node1->next == node1 )
	{
		node1->next = node2;
	}
	if ( node2->next == node2 )
	{
		node2->next = node1;
	}
	if ( node1->next )
	{
		node1->next->prev = node1;
	}
	if ( node2->next )
	{
		node2->next->prev = node2;
	}
	if ( node1->prev )
	{
		node1->prev->next = node1;
	}
	if ( node2->prev )
	{
		node2->prev->next = node2;
	}
}

/* Do the increments */
static void increment( huff_t* huff, node_t *node )
{
	node_t *lnode;

	if ( !node )
	{
		return;
	}

	if ( node->next != NULL && node->next->weight == node->weight )
	{
		lnode = *node->head;
		if ( lnode != node->parent )
		{
			swap( huff, lnode, node );
		}
		swaplist( lnode, node );
	}
	if ( node->prev && node->prev->weight == node->weight )
	{
		*node->head = node->prev;
	}
	else
	{
		*node->head = NULL;
		free_ppnode( huff, node->head );
	}
	node->weight++;
	if ( node->next && node->next->weight == node->weight )
	{
		node->head = node->next->head;
	}
	else
	{
		node->head = get_ppnode( huff );
		*node->head = node;
	}
	if ( node->parent )
	{
		increment( huff, node->parent );
		if ( node->prev == node->parent )
		{
			swaplist( node, node->parent );
			if ( *node->head == node )
			{
				*node->head = node->parent;
			}
		}
	}
}

void Huff_addRef( huff_t* huff, byte ch )
{
	node_t *tnode, *tnode2;
	if ( huff->loc[ch] == NULL )   /* if this is the first transmission of this node */
	{
		tnode = &( huff->nodeList[huff->blocNode++] );
		tnode2 = &( huff->nodeList[huff->blocNode++] );

		tnode2->symbol = INTERNAL_NODE;
		tnode2->weight = 1;
		tnode2->next = huff->lhead->next;
		if ( huff->lhead->next )
		{
			huff->lhead->next->prev = tnode2;
			if ( huff->lhead->next->weight == 1 )
			{
				tnode2->head = huff->lhead->next->head;
			}
			else
			{
				tnode2->head = get_ppnode( huff );
				*tnode2->head = tnode2;
			}
		}
		else
		{
			tnode2->head = get_ppnode( huff );
			*tnode2->head = tnode2;
		}
		huff->lhead->next = tnode2;
		tnode2->prev = huff->lhead;

		tnode->symbol = ch;
		tnode->weight = 1;
		tnode->next = huff->lhead->next;
		if ( huff->lhead->next )
		{
			huff->lhead->next->prev = tnode;
			if ( huff->lhead->next->weight == 1 )
			{
				tnode->head = huff->lhead->next->head;
			}
			else
			{
				/* this should never happen */
				tnode->head = get_ppnode( huff );
				*tnode->head = tnode2;
			}
		}
		else
		{
			/* this should never happen */
			tnode->head = get_ppnode( huff );
			*tnode->head = tnode;
		}
		huff->lhead->next = tnode;
		tnode->prev = huff->lhead;
		tnode->left = tnode->right = NULL;

		if ( huff->lhead->parent )
		{
			if ( huff->lhead->parent->left == huff->lhead )   /* lhead is guaranteed to by the NYT */
			{
				huff->lhead->parent->left = tnode2;
			}
			else
			{
				huff->lhead->parent->right = tnode2;
			}
		}
		else
		{
			huff->tree = tnode2;
		}

		tnode2->right = tnode;
		tnode2->left = huff->lhead;

		tnode2->parent = huff->lhead->parent;
		huff->lhead->parent = tnode->parent = tnode2;

		huff->loc[ch] = tnode;

		increment( huff, tnode2->parent );
	}
	else
	{
		increment( huff, huff->loc[ch] );
	}
}

/* Get a symbol */
int Huff_Receive( node_t *node, int *ch, byte *fin )
{
	while ( node && node->symbol == INTERNAL_NODE )
	{
		if ( get_bit( fin ) )
		{
			node = node->right;
		}
		else
		{
			node = node->left;
		}
	}
	if ( !node )
	{
		return 0;
//		Com_Error(ERR_DROP, "Illegal tree!\n");
	}
	return ( *ch = node->symbol );
}

/* Get a symbol */
void Huff_offsetReceive( node_t *node, int *ch, byte *fin, int *offset )
{
	bloc = *offset;
	while ( node && node->symbol == INTERNAL_NODE )
	{
		if ( get_bit( fin ) )
		{
			node = node->right;
		}
		else
		{
			node = node->left;
		}
	}
	if ( !node )
	{
		*ch = 0;
		return;
//		Com_Error(ERR_DROP, "Illegal tree!\n");
	}
	*ch = node->symbol;
	*offset = bloc;
}

/* Send the prefix code for this node */
static void send( node_t *node, node_t *child, byte *fout )
{
	if ( node->parent )
	{
		send( node->parent, node, fout );
	}
	if ( child )
	{
		if ( node->right == child )
		{
			add_bit( 1, fout );
		}
		else
		{
			add_bit( 0, fout );
		}
	}
}

/* Send a symbol */
void Huff_transmit( huff_t *huff, int ch, byte *fout )
{
	int i;
	if ( huff->loc[ch] == NULL )
	{
		/* node_t hasn't been transmitted, send a NYT, then the symbol */
		Huff_transmit( huff, NYT, fout );
		for ( i = 7; i >= 0; i-- )
		{
			add_bit( (char)( ( ch >> i ) & 0x1 ), fout );
		}
	}
	else
	{
		send( huff->loc[ch], NULL, fout );
	}
}

void Huff_offsetTransmit( huff_t *huff, int ch, byte *fout, int *offset )
{
	bloc = *offset;
	send( huff->loc[ch], NULL, fout );
	*offset = bloc;
}

void Huff_Decompress( msg_t *mbuf, int offset )
{
	int ch, cch, i, j, size;
	byte seq[65536];
	byte*       buffer;
	huff_t huff;

	size = mbuf->cursize - offset;
	buffer = mbuf->data + offset;

	if ( size <= 0 )
	{
		return;
	}

	Com_Memset( &huff, 0, sizeof( huff_t ) );
	// Initialize the tree & list with the NYT node
	huff.tree = huff.lhead = huff.ltail = huff.loc[NYT] = &( huff.nodeList[huff.blocNode++] );
	huff.tree->symbol = NYT;
	huff.tree->weight = 0;
	huff.lhead->next = huff.lhead->prev = NULL;
	huff.tree->parent = huff.tree->left = huff.tree->right = NULL;

	cch = buffer[0] * 256 + buffer[1];
	// don't overflow with bad messages
	if ( cch > mbuf->maxsize - offset )
	{
		cch = mbuf->maxsize - offset;
	}
	bloc = 16;

	for ( j = 0; j < cch; j++ )
	{
		ch = 0;
		// don't overflow reading from the messages
		// FIXME: would it be better to have a overflow check in get_bit ?
		if ( ( bloc >> 3 ) > size )
		{
			seq[j] = 0;
			break;
		}
		Huff_Receive( huff.tree, &ch, buffer );               /* Get a character */
		if ( ch == NYT )                                /* We got a NYT, get the symbol associated with it */
		{
			ch = 0;
			for ( i = 0; i < 8; i++ )
			{
				ch = ( ch << 1 ) + get_bit( buffer );
			}
		}

		seq[j] = ch;                                    /* Write symbol */

		Huff_addRef( &huff, (byte)ch );                               /* Increment node */
	}
	mbuf->cursize = cch + offset;
	Com_Memcpy( mbuf->data + offset, seq, cch );
}

extern int oldsize;

void Huff_Compress( msg_t *mbuf, int offset )
{
	int i, ch, size;
	byte seq[65536];
	byte*       buffer;
	huff_t huff;

	size = mbuf->cursize - offset;
	buffer = mbuf->data + + offset;

	if ( size <= 0 )
	{
		return;
	}

	Com_Memset( &huff, 0, sizeof( huff_t ) );
	// Add the NYT (not yet transmitted) node into the tree/list */
	huff.tree = huff.lhead = huff.loc[NYT] =  &( huff.nodeList[huff.blocNode++] );
	huff.tree->symbol = NYT;
	huff.tree->weight = 0;
	huff.lhead->next = huff.lhead->prev = NULL;
	huff.tree->parent = huff.tree->left = huff.tree->right = NULL;
	huff.loc[NYT] = huff.tree;

	seq[0] = ( size >> 8 );
	seq[1] = size & 0xff;

	bloc = 16;

	for ( i = 0; i < size; i++ )
	{
		ch = buffer[i];
		Huff_transmit( &huff, ch, seq );                      /* Transmit symbol */
		Huff_addRef( &huff, (byte)ch );                               /* Do update */
	}

	bloc += 8;                                              // next byte

	mbuf->cursize = ( bloc >> 3 ) + offset;
	Com_Memcpy( mbuf->data + offset, seq, ( bloc >> 3 ) );
}

void Huff_Init( huffman_t *huff )
{

	Com_Memset( &huff->compressor, 0, sizeof( huff_t ) );
	Com_Memset( &huff->decompressor, 0, sizeof( huff_t ) );

	// Initialize the tree & list with the NYT node
	huff->decompressor.tree = huff->decompressor.lhead = huff->decompressor.ltail = huff->decompressor.loc[NYT] = &( huff->decompressor.nodeList[huff->decompressor.blocNode++] );
	huff->decompressor.tree->symbol = NYT;
	huff->decompressor.tree->weight = 0;
	huff->decompressor.lhead->next = huff->decompressor.lhead->prev = NULL;
	huff->decompressor.tree->parent = huff->decompressor.tree->left = huff->decompressor.tree->right = NULL;

	// Add the NYT (not yet transmitted) node into the tree/list */
	huff->compressor.tree = huff->compressor.lhead = huff->compressor.loc[NYT] =  &( huff->compressor.nodeList[huff->compressor.blocNode++] );
	huff->compressor.tree->symbol = NYT;
	huff->compressor.tree->weight = 0;
	huff->compressor.lhead->next = huff->compressor.lhead->prev = NULL;
	huff->compressor.tree->parent = huff->compressor.tree->left = huff->compressor.tree->right = NULL;
	huff->compressor.loc[NYT] = huff->compressor.tree;
}
// END huffman.c from Enemy Territory

void MSG_initHuffman()
{
	int i,j;

	msgInit = qtrue;
	Huff_Init(&msgHuff);
	for(i=0; i<256; i++)
	{
		for (j=0; j<msg_hData[i]; j++)
		{
			Huff_addRef(&msgHuff.compressor,	(byte)i);			// Do update
			Huff_addRef(&msgHuff.decompressor,	(byte)i);			// Do update
		}
	}
}

void MSG_Init( msg_t *buf, byte *data, int length )
{
	if (!msgInit)
	{
		MSG_initHuffman();
	}
	buf->data = data;
	buf->maxsize = length;
	buf->overflowed = qfalse;
	buf->cursize = 0;
	buf->readcount = 0;
	buf->bit = 0;
}

int MSG_ReadBitsCompress(const byte* input, int readsize, byte* outputBuf, int outputBufSize)
{
	readsize = readsize * 8;
	byte *outptr = outputBuf;

	int get;
	int offset;
	int i;

	if(readsize <= 0)
	{
		return 0;
	}

	for(offset = 0, i = 0; offset < readsize && i < outputBufSize; i++)
	{
		Huff_offsetReceive( msgHuff.decompressor.tree, &get, (byte*)input, &offset);
		*outptr = (byte)get;
		outptr++;
	}
	return i;
}

int MSG_WriteBitsCompress( const byte *datasrc, byte *buffdest, int bytecount)
{

	int offset;
	int i;

	if(bytecount <= 0)
	{
		return 0;
	}

	for(offset = 0, i = 0; i < bytecount; i++)
	{
		Huff_offsetTransmit( &msgHuff.compressor, (int)datasrc[i], buffdest, &offset );
	}
	return (offset + 7) / 8;
}

int MSG_GetByte(msg_t *msg, int where)
{
	return msg->data[where];
}

int MSG_GetShort(msg_t *msg, int where)
{
	return *(int16_t*)&msg->data[where];
}

int MSG_GetLong(msg_t *msg, int where)
{
	return *(int32_t*)&msg->data[where];
}

int MSG_ReadByte( msg_t *msg )
{
	byte	c;

	if ( msg->readcount+sizeof(byte) > msg->cursize )
	{
		msg->overflowed = 1;
		return -1;
	}
	c = MSG_GetByte(msg, msg->readcount);
	msg->readcount += sizeof(byte);
	return c;
}

int MSG_ReadShort( msg_t *msg )
{
	int16_t	c;

	if ( msg->readcount+sizeof(short) > msg->cursize )
	{
		msg->overflowed = 1;
		return -1;
	}
	c = MSG_GetShort(msg, msg->readcount);
	msg->readcount += sizeof(short);
	return c;
}

int32_t MSG_ReadLong( msg_t *msg )
{
	int32_t	c;

	if ( msg->readcount+sizeof(int32_t) > msg->cursize )
	{
		msg->overflowed = 1;
		return -1;
	}
	c = MSG_GetLong(msg, msg->readcount);
	msg->readcount += sizeof(int32_t);
	return c;
}

#define BIG_INFO_STRING 8192
char *MSG_ReadBigString( msg_t *msg )
{
	static char string[BIG_INFO_STRING];
	int l,c;

	l = 0;
	do
	{
		c = MSG_ReadByte( msg );      // use ReadByte so -1 is out of bounds
		if ( c == -1 || c == 0 )
		{
			break;
		}
		// translate all fmt spec to avoid crash bugs
		if ( c == '%' )
		{
			c = '.';
		}

		string[l] = c;
		l++;
	}
	while ( l < sizeof( string ) - 1 );

	string[l] = 0;

	return string;
}

int MSG_ReadBits( msg_t *msg, int bits )
{
	int		value;
	int		valueBits;
	int		get;
	int		fraction;
	qboolean	sgn;

	value = 0;
	valueBits = 0;

	if ( bits < 0 )
	{
		bits = -bits;
		sgn = qtrue;
	}
	else
	{
		sgn = qfalse;
	}

	while ( valueBits < bits )
	{
		if ( msg->bit == 0 )
		{
			msg->readcount++;
		}
		get = 8 - msg->bit;
		if ( get > (bits - valueBits) )
		{
			get = (bits - valueBits);
		}
		fraction = msg->data[msg->readcount - 1];
		fraction >>= msg->bit;
		fraction &= ( 1 << get ) - 1;
		value |= fraction << valueBits;

		valueBits += get;
		msg->bit = ( msg->bit + get ) & 7;
	}

	if ( sgn )
	{
		if ( value & ( 1 << ( bits - 1 ) ) )
		{
			value |= -1 ^ ( ( 1 << bits ) - 1 );
		}
	}

	return value;
}

int FS_Read( void *buffer, int len, FILE *f )
{
	return fread( buffer, 1, len, f );
}

void CL_DemoCompleted(void)
{
}

void SHOWNET( msg_t *msg, char *s )
{
	Com_Printf( "%3i:%s\n", msg->readcount - 1, s );
}

gameState_t gameState;
entityState_t entityBaselines[MAX_GENTITIES];
void CL_ParseGamestate( msg_t *msg )
{
	int i;
	entityState_t   *es;
	int newnum;
	entityState_t nullstate;
	int cmd;
	char            *s;

	// a gamestate always marks a server command sequence
	int serverCommandSequence = MSG_ReadLong( msg );

	// parse all the configstrings and baselines
	gameState.dataCount = 1; // leave a 0 at the beginning for uninitialized configstrings
	while ( 1 )
	{
		cmd = MSG_ReadByte( msg );

		if ( cmd == svc_EOF )
		{
			break;
		}

		if ( cmd == svc_configstring )
		{
			int len;

			i = MSG_ReadShort( msg );
			if ( i < 0 || i >= MAX_CONFIGSTRINGS )
			{
				Com_Error( ERR_DROP, "configstring > MAX_CONFIGSTRINGS" );
			}
			s = MSG_ReadBigString( msg );

			len = strlen( s );
			Com_Printf("%s\n", s);

			if ( len + 1 + gameState.dataCount > MAX_GAMESTATE_CHARS )
			{
				Com_Error( ERR_DROP, "MAX_GAMESTATE_CHARS exceeded" );
			}

			// append it to the gameState string buffer
			gameState.stringOffsets[ i ] = gameState.dataCount;
			memcpy( gameState.stringData + gameState.dataCount, s, len + 1 );
			gameState.dataCount += len + 1;
		}
		else if ( cmd == svc_baseline )
		{
			newnum = MSG_ReadBits( msg, GENTITYNUM_BITS );
			if ( newnum < 0 || newnum >= MAX_GENTITIES )
			{
				Com_Error( ERR_DROP, "Baseline number out of range: %i", newnum );
			}
			memset( &nullstate, 0, sizeof( nullstate ) );
			es = &entityBaselines[ newnum ];
			//MSG_ReadDeltaEntity( msg, &nullstate, es, newnum );
		}
		else
		{
			Com_Error( ERR_DROP, "CL_ParseGamestate: bad command byte" );
		}
	}

	int clientNum = MSG_ReadLong( msg );
	// read the checksum feed
	int checksumFeed = MSG_ReadLong( msg );
}

void CL_ParseServerMessage( msg_t *msg )
{
	int cmd;
	int reliableAcknowledge;
	byte buffer[MAX_MSGLEN];
	msg_t decompressMsg;

	// get the reliable sequence acknowledge number
	reliableAcknowledge = MSG_ReadLong( msg );

	MSG_Init(&decompressMsg, buffer, sizeof(buffer));
	decompressMsg.cursize = MSG_ReadBitsCompress(msg->data + msg->readcount, msg->cursize - msg->readcount, decompressMsg.data, decompressMsg.maxsize);

	//
	// parse the message
	//
	while ( 1 )
	{
		if ( decompressMsg.readcount > decompressMsg.cursize )
		{
			Com_Error( ERR_DROP,"CL_ParseServerMessage: read past end of server message" );
			break;
		}

		cmd = MSG_ReadByte( &decompressMsg );

		if ( cmd == svc_EOF )
		{
			SHOWNET( &decompressMsg, "END OF MESSAGE\n" );
			break;
		}

		if ( !svc_strings[cmd] )
		{
			Com_Printf( "%3i:BAD CMD %i\n", decompressMsg.readcount - 1, cmd );
		}
		else
		{
			SHOWNET( &decompressMsg, svc_strings[cmd] );
		}

		// other commands
		switch ( cmd )
		{
		default:
			Com_Error( ERR_DROP,"CL_ParseServerMessage: Illegible server message %d\n", cmd );
			break;
		case svc_nop:
			Com_Printf("svc_nop\n");
			break;
		case svc_serverCommand:
			Com_Printf("svc_serverCommand\n");
			//CL_ParseCommandString( &decompressMsg );
			break;
		case svc_gamestate:
			Com_Printf("svc_gamestate\n");
			CL_ParseGamestate( &decompressMsg );
			break;
		case svc_snapshot:
			Com_Printf("svc_snapshot\n");
			//CL_ParseSnapshot( &decompressMsg );
			break;
		case svc_download:
			Com_Printf("svc_download\n");
			break;
		}
	}
}

void CL_ReadDemoMessage( void )
{
	int r;
	msg_t buf;
	byte bufData[ MAX_MSGLEN ];
	int s;

	if ( !demo.demofile )
	{
		CL_DemoCompleted();
		return;
	}

	// get the sequence number
	r = FS_Read( &s, 4, demo.demofile );
	if ( r != 4 )
	{
		CL_DemoCompleted();
		return;
	}

	// init the message
	MSG_Init( &buf, bufData, sizeof( bufData ) );

	// get the length
	r = FS_Read( &buf.cursize, 4, demo.demofile );

	if ( r != 4 )
	{
		CL_DemoCompleted();
		return;
	}
	buf.cursize = LittleLong( buf.cursize );
	if ( buf.cursize == -1 )
	{
		CL_DemoCompleted();
		return;
	}
	if ( buf.cursize > buf.maxsize )
	{
		Com_Error( ERR_DROP, "CL_ReadDemoMessage: demoMsglen > MAX_MSGLEN" );
	}
	r = FS_Read( buf.data, buf.cursize, demo.demofile );
	if ( r != buf.cursize )
	{
		Com_Printf( "Demo file was truncated.\n" );
		CL_DemoCompleted();
		return;
	}

	CL_ParseServerMessage( &buf );
}

int FS_FOpenFileRead( const char *filename, FILE **file, qboolean uniqueFILE )
{
	*file = fopen( filename, "rb" );
	return ( *file != NULL );
}

int main( int argc, char **argv )
{
	//printf("Test %d\n", COD_VERSION);
	//printf("Test %d\n", MAX_MSGLEN);
	//printf("Test %d\n", sizeof(client_t));
	//printf("Test %d\n", sizeof(huff_t));

	if( argc < 2 )
	{
		Com_Error( ERR_FATAL, "Usage: cod2demo [demofile]\n" );
	}

	FS_FOpenFileRead( argv[1], &demo.demofile, qtrue );
	CL_ReadDemoMessage();
	fclose( demo.demofile );

	return 1;
}