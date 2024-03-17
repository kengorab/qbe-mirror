#include "all.h"

Amd64Op amd64_op[NOp] = {
#define O(op, t, x) [O##op] =
#define X(nm, zf, lf) { nm, zf, lf, },
	#include "../ops.h"
};

static int
amd64_memargs(int op)
{
	return amd64_op[op].nmem;
}

#define AMD64_COMMON \
	.gpr0 = RAX, \
	.ngpr = NGPR, \
	.fpr0 = XMM0, \
	.nfpr = NFPR, \
	.rglob = BIT(RBP) | BIT(RSP), \
	.nrglob = 2, \
	.nrsave = {NGPS, NFPS}, \
	.memargs = amd64_memargs, \
	.abi0 = elimsb, \
	.isel = amd64_isel, \
	.emitfn = amd64_emitfn, \

Target T_amd64_sysv = {
	.name = "amd64_sysv",
	.emitfin = elf_emitfin,
	.asloc = ".L",
	.abi1 = amd64_sysv_abi,
	.retregs = amd64_sysv_retregs,
	.argregs = amd64_sysv_argregs,
	.rsave = amd64_sysv_rsave,
	AMD64_COMMON
};

Target T_amd64_apple = {
	.name = "amd64_apple",
	.apple = 1,
	.emitfin = macho_emitfin,
	.asloc = "L",
	.assym = "_",
	.abi1 = amd64_sysv_abi,
	.retregs = amd64_sysv_retregs,
	.argregs = amd64_sysv_argregs,
	.rsave = amd64_sysv_rsave,
	AMD64_COMMON
};

Target T_amd64_win = {
	.name = "amd64_win",
	.windows = 1,
	.emitfin = win_emitfin,
	.asloc = ".L",
	.abi1 = amd64_winabi_abi,
	.retregs = amd64_winabi_retregs,
	.argregs = amd64_winabi_argregs,
	.rsave = amd64_winabi_rsave,
	AMD64_COMMON
};
