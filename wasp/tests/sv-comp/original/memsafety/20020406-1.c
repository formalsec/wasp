extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

/* Origin: abbott@dima.unige.it
 * PR c/5120
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned int FFelem;

FFelem FFmul(const FFelem x, const FFelem y)
{
  return x;
}


struct DUPFFstruct
{
  int maxdeg;
  int deg;
  FFelem *coeffs;
};

typedef struct DUPFFstruct *DUPFF;


int DUPFFdeg(const DUPFF f)
{
  return f->deg;
}


DUPFF DUPFFnew(const int maxdeg)
{
  DUPFF ans = (DUPFF)malloc(sizeof(struct DUPFFstruct));
  ans->coeffs = 0;
  if (maxdeg >= 0) {
    ans->coeffs = (FFelem*)malloc((maxdeg+1)*sizeof(FFelem));
    memset(ans->coeffs, 0, (maxdeg+1)*sizeof(FFelem));
  }
  ans->maxdeg = maxdeg;
  ans->deg = -1;
  return ans;
}

void DUPFFfree(DUPFF x)
{
}

void DUPFFswap(DUPFF x, DUPFF y)
{
}


DUPFF DUPFFcopy(const DUPFF x)
{
  return x;
}


void DUPFFshift_add(DUPFF f, const DUPFF g, int deg, const FFelem coeff)
{
}


DUPFF DUPFFexgcd(DUPFF *fcofac, DUPFF *gcofac, const DUPFF f, const DUPFF g)
{
  DUPFF u, v, uf, ug, vf, vg;
  FFelem q, lcu, lcvrecip, p;
  int df, dg, du, dv;

  if (DUPFFdeg(f) < DUPFFdeg(g)) return DUPFFexgcd(gcofac, fcofac, g, f);
  if (DUPFFdeg(f) != 2 || DUPFFdeg(g) != 1) abort();
  if (f->coeffs[0] == 0) return f;
  p = 2;

  df = DUPFFdeg(f);  if (df < 0) df = 0; /* both inputs are zero */
  dg = DUPFFdeg(g);  if (dg < 0) dg = 0; /* one input is zero */
  u = DUPFFcopy(f);
  v = DUPFFcopy(g);

  uf = DUPFFnew(dg); uf->coeffs[0] = 1; uf->deg = 0;
  ug = DUPFFnew(df);
  vf = DUPFFnew(dg);
  vg = DUPFFnew(df); vg->coeffs[0] = 1; vg->deg = 0;

  while (DUPFFdeg(v) > 0)
  {
    dv = DUPFFdeg(v);
    lcvrecip = FFmul(1, v->coeffs[dv]);
    while (DUPFFdeg(u) >= dv)
    {
      du = DUPFFdeg(u);
      lcu = u->coeffs[du];
      q = FFmul(lcu, lcvrecip);
      DUPFFshift_add(u, v, du-dv, p-q);
      DUPFFshift_add(uf, vf, du-dv, p-q);
      DUPFFshift_add(ug, vg, du-dv, p-q);
    }
    DUPFFswap(u, v);
    DUPFFswap(uf, vf);
    DUPFFswap(ug, vg);
  }
  if (DUPFFdeg(v) == 0)
  {
    DUPFFswap(u, v);
    DUPFFswap(uf, vf);
    DUPFFswap(ug, vg);
  }
  DUPFFfree(vf);
  DUPFFfree(vg);
  DUPFFfree(v);
  *fcofac = uf;
  *gcofac = ug;
  return u;
}



int main()
{
  DUPFF f, g, cf, cg, h;
  f = DUPFFnew(1); f->coeffs[1] = 1; f->deg = 1;
  g = DUPFFnew(2); g->coeffs[2] = 1; g->deg = 2;

  h = DUPFFexgcd(&cf, &cg, f, g);
  h = h;
  return 0;
}
