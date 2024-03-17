#include "../all.h"

typedef struct Amd64Op Amd64Op;

enum Amd64Reg {
	/* |Register    | SysV             | WinABI           | */
	/* +------------+------------------+------------------+ */
	RAX = RXX+1, /* | caller-save (v)  | caller-save (v)  | */
	RCX,         /* | caller-save (v)  | caller-save (v)  | */
	RDX,         /* | caller-save (v)  | caller-save (v)  | */
	RSI,         /* | caller-save (v)  | callee-save (nv) | */
	RDI,         /* | caller-save (v)  | callee-save (nv) | */
	R8,          /* | caller-save (v)  | caller-save (v)  | */
	R9,          /* | caller-save (v)  | caller-save (v)  | */
	R10,         /* | caller-save (v)  | caller-save (v)  | */
	R11,         /* | caller-save (v)  | caller-save (v)  | */
	             /* +------------------+------------------+ */
	RBX,         /* | callee-save (nv) | callee-save (nv) | */
	R12,         /* | callee-save (nv) | callee-save (nv) | */
	R13,         /* | callee-save (nv) | callee-save (nv) | */
	R14,         /* | callee-save (nv) | callee-save (nv) | */
	R15,         /* | callee-save (nv) | callee-save (nv) | */
				 /* +------------------+------------------+ */
	RBP,         /* | globally live    | callee-save (nv) | */
	RSP,         /* | globally live    | callee-save (nv) | */

	XMM0, /* sse */
	XMM1,
	XMM2,
	XMM3,
	XMM4,
	XMM5,
	XMM6,
	XMM7,
	XMM8,
	XMM9,
	XMM10,
	XMM11,
	XMM12,
	XMM13,
	XMM14,
	XMM15,

	NFPR = XMM14 - XMM0 + 1, /* reserve XMM15 */
	NGPR = RSP - RAX + 1,
	NGPS = R11 - RAX + 1,
	NFPS = NFPR,
	NCLR = R15 - RBX + 1,
};
MAKESURE(reg_not_tmp, XMM15 < (int)Tmp0);

struct Amd64Op {
	char nmem;
	char zflag;
	char lflag;
};

/* targ.c */
extern Amd64Op amd64_op[];

/* sysv.c (abi) */
extern int amd64_sysv_rsave[];
extern int amd64_sysv_rclob[];
bits amd64_sysv_retregs(Ref, int[2]);
bits amd64_sysv_argregs(Ref, int[2]);
void amd64_sysv_abi(Fn *);

/* winabi.c (abi) */
extern int amd64_winabi_rsave[];
extern int amd64_winabi_rclob[];
bits amd64_winabi_retregs(Ref, int[2]);
bits amd64_winabi_argregs(Ref, int[2]);
void amd64_winabi_abi(Fn *);

/* isel.c */
void amd64_isel(Fn *);

/* emit.c */
void amd64_emitfn(Fn *, FILE *);
