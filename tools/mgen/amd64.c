#include <stdio.h>
#include "../../all.h"

typedef struct Num Num;

struct Num {
	uchar n;
	uchar nl, nr;
	Ref l, r;
};

enum {
	Pob,
	Pbms,
	Pobms,
	Pbm1,
	Pobm1,
};

/* mgen generated code
 *
 * (with-vars (o b m s)
 *   (patterns
 *     (ob   (add (con o) (tmp b)))
 *     (bms  (add (tmp b) (mul (tmp m) (con s 1 2 4 8))))
 *     (obms (add (con o) (tmp b) (mul (tmp m) (con s 1 2 4 8))))
 *     (bm1  (add (tmp b) (tmp m)))
 *     (obm1 (add (con o) (tmp b) (tmp m)))
 * ))
 */

static int
opn(int op, int l, int r)
{
	static uchar Oaddtbl[91] = {
		2,
		2,2,
		5,5,3,
		8,8,3,3,
		10,10,6,6,6,
		5,5,7,7,9,7,
		12,12,3,3,6,7,3,
		8,8,3,3,6,7,3,3,
		5,5,7,7,9,7,7,7,7,
		12,12,3,3,6,7,3,3,7,3,
		5,5,11,11,9,11,11,11,11,11,11,
		8,8,3,3,6,7,3,3,7,3,11,3,
		5,5,7,7,9,7,7,7,7,7,11,7,7,
	};
	int t;

	if (l < r) {
		t = l;
		l = r;
		r = t;
	}
	switch (op) {
	case Omul:
		if (2 <= l)
		if (r == 0) {
			return 4;
		}
		return 2;
	case Oadd:
		return Oaddtbl[(l + l*l)/2 + r];
	default:
		return 2;
	}
}

static int
refn(Ref r, Num *tn, Con *con)
{
	int64_t n;

	switch (rtype(r)) {
	case RTmp:
		if (!tn[r.val].n)
			tn[r.val].n = 2;
		return tn[r.val].n;
	case RCon:
		if (con[r.val].type != CBits)
			return 1;
		n = con[r.val].bits.i;
		if (n == 8 || n == 4 || n == 2 || n == 1)
			return 0;
		return 1;
	default:
		die("unreachable");
	}
}

static bits match[13] = {
	[3] = BIT(Pbm1),
	[5] = BIT(Pob),
	[6] = BIT(Pbm1) | BIT(Pbms),
	[7] = BIT(Pbm1) | BIT(Pobm1),
	[8] = BIT(Pob) | BIT(Pobm1),
	[9] = BIT(Pbm1) | BIT(Pbms) | BIT(Pobm1) | BIT(Pobms),
	[10] = BIT(Pob),
	[11] = BIT(Pbm1) | BIT(Pobm1) | BIT(Pobms),
	[12] = BIT(Pob) | BIT(Pobm1) | BIT(Pobms),
};

static uchar *matcher[] = {
	[Pbm1] = (uchar[]){
		1,3,1,3,2,0
	},
	[Pbms] = (uchar[]){
		5,1,6,5,27,1,5,1,4,5,13,1,3,3,3,2,3,1,0,3,
		1,1,3,3,3,2,0,1,21
	},
	[Pob] = (uchar[]){
		1,3,0,3,1,0
	},
	[Pobm1] = (uchar[]){
		5,3,7,9,9,33,11,35,47,1,5,3,12,9,8,9,5,9,
		17,1,3,0,3,1,3,2,0,3,1,1,3,0,34,1,37,1,5,3,
		10,9,8,9,5,9,10,29,37,1,3,0,1,32
	},
	[Pobms] = (uchar[]){
		5,2,9,7,11,19,45,1,1,3,3,3,2,1,3,0,3,1,0,1,
		5,1,10,5,14,1,3,0,1,3,3,3,2,26,3,1,1,3,0,1,
		3,3,3,2,0,1,3,0,5,1,6,5,15,1,5,1,4,5,6,38,
		3,1,49,1,38
	},
};

/* end of generated code */

void
runmatch(uchar *code, Num *tn, Ref ref, Ref *vars)
{
	Ref stkbuf[20], *stk;
	uchar *s, *pc;
	int bc, i;
	int n, nl, nr;

	assert(rtype(ref) == RTmp);
	stk = stkbuf;
	pc = code;
	while ((bc = *pc))
		switch (bc) {
		case 1: /* pushsym */
		case 2: /* push */
			assert(stk < &stkbuf[20]);
			assert(rtype(ref) == RTmp);
			nl = tn[ref.val].nl;
			nr = tn[ref.val].nr;
			if (bc == 1 && nl > nr) {
				*stk++ = tn[ref.val].l;
				ref = tn[ref.val].r;
			} else {
				*stk++ = tn[ref.val].r;
				ref = tn[ref.val].l;
			}
			pc++;
			break;
		case 3: /* set */
			vars[*++pc] = ref;
			if (*(pc + 1) == 0)
				return;
			/* fall through */
		case 4: /* pop */
			assert(stk > &stkbuf[0]);
			ref = *--stk;
			pc++;
			break;
		case 5: /* switch */
			assert(rtype(ref) == RTmp);
			n = tn[ref.val].n;
			s = pc + 1;
			for (i=*s++; i>0; i--, s++)
				if (n == *s++)
					break;
			pc += *s;
			break;
		default: /* jump */
			assert(bc >= 10);
			pc = code + (bc - 10);
			break;
		}
}
