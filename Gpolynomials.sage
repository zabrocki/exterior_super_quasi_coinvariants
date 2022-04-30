def pring(n):
    """
    Polynomial ring where the bosonic variables live
    """
    return PolynomialRing(QQ,['x'+ascii(i) for i in range(n)])

def BR(n):
    """
    The exterior algebra in n variables t1,t2,...,tn with coefficients
    that are polynomials in n variables x1,x2,...,xn
    """
    P = pring(n)
    return ExteriorAlgebra(P, ['t'+ascii(i) for i in range(n)])

def inject_variables(n):
    BR(n).inject_variables()
    BR(n).base_ring().inject_variables()

def gens(n):
    """
    The list of variables (x1,x2,...,xn,t1,t2,...,tn)
    """
    return BR(n).base_ring().gens() + BR(n).gens()

def num_trailing_zeros(A):
    """
    The number of trailing zeros in the array
    """
    B = list(zip(A[0],A[1]))
    return max([k for k in range(len(B)+1) if all(b==(0,0) for b in B[len(B)-k:])])

def is_gen_comp(A):
    """
    A pair of lists of integers, first one has non-negative entries
    the second has entries in {0,1}
    """
    if len(A[0])!=len(A[1]):
        return False
    return all(a>=0 for a in A[0]) and all(a in [0,1] for a in A[1])

def is_bicomp(A):
    """
    A pair A = [A[0], A[1]] where all entries in A[0] >= 0 and all
    entries in A[1] in {0,1} and there are no A[0][i]==A[1][i]==0
    except at the end
    """
    if len(A[0])!=len(A[1]):
        return False
    if len(A[0])==0 or all(not a for a in A[0]+A[1]):
        return True
    k = num_trailing_zeros(A)
    return all(a>=0 for a in A[0]) and\
        all(a in [0,1] for a in A[1]) and\
        all(a!=(0,0) for a in zip(A[0][:len(A[0])-k],A[1][:len(A[0])-k]))

def upv(POLY):
    """
    Raise the x-variables by one and embed in the next larger polynomial ring
    """
    n = len(POLY.parent().gens())
    P = pring(n+1)
    vs = P.gens()
    if n==1: # polynomial rings with single variables look different internally
        return P.sum(cc*vs[1]**tt for (tt,cc) in POLY.dict().items())
    else:
        return P.sum(cc*P.prod(vs[i+1]**tt[i] for i in range(len(tt)))\
            for (tt,cc) in POLY.dict().items())

def upvars(SPOLY):
    """
    Raise the x and t variables by one and embed in the next larger exterior
    algebra
    """
    n = len(SPOLY.parent().gens())
    P = BR(n+1)
    return P._from_dict(dict([(tuple(i+1 for i in tt),upv(cc))\
        for (tt,cc) in SPOLY.monomial_coefficients().items()]))

def F(A):
    """
    The fundamental quasi-symmetric function indexed by the bicomposition A
    """
    if not is_bicomp(A):
        raise ValueError("%s\n%s is not a bicomposition."%(A[0],A[1]))
    n = len(A[0])
    np = len(A[0])-num_trailing_zeros(A)
    if all(not a for a in A[0]+A[1]):
        return BR(n).one()
    vrs = gens(n)
    if A[0][0]>1 or (A[0][0]==1 and A[1][0]==1):
        if n==np:
            return vrs[0]*F([[A[0][0]-1]+A[0][1:],A[1]])
        else:
            return vrs[0]*F([[A[0][0]-1]+A[0][1:],A[1]]) +\
                upvars(F([A[0][:n-1],A[1][:n-1]]))
    elif A[0][0]==1 and A[1][0]==0:
        if n==np:
            return vrs[0]*upvars(F([A[0][1:],A[1][1:]]))
        else:
            return vrs[0]*upvars(F([A[0][1:],A[1][1:]])) +\
                upvars(F([A[0][:n-1],A[1][:n-1]]))
    elif A[0][0]==0 and A[1][0]==1:
        if n==np:
            return vrs[n]*upvars(F([A[0][1:],A[1][1:]]))
        else:
            return  vrs[n]*upvars(F([A[0][1:],A[1][1:]]))+upvars(F([A[0][:n-1],A[1][:n-1]]))

def last_zz(A):
    if is_bicomp(A):
        raise ValueError("%s\n%s is already a bicomposition."%(A[0],A[1]))
    for i in range(len(A[0])):
        if A[0][i]==0 and A[1][i]==0 and is_bicomp([A[0][i+1:],A[1][i+1:]]):
            return i

def split(A):
    k = last_zz(A)
    if k==0:
        U = [[],[]]
    else:
        U = [A[0][:k],A[1][:k]]
    (a,b) = (A[0][k+1], A[1][k+1])
    B = [A[0][k+2:],A[1][k+2:]]
    return (k,U,a,b,B)

def G(A):
    if not is_gen_comp(A):
        raise ValueError("%s\n%s is not a bicomposition"%(A[0],A[1]))
    if is_bicomp(A):
        return F(A)
    (k,U,a,b,B) = split(A)
    n = len(A[0])
    vrs = gens(n)
    if a>0:
        return  G([U[0]+[a]+B[0]+[0],U[1]+[b]+B[1]+[0]])-vrs[k]*G([U[0]+[a-1]+B[0]+[0],U[1]+[b]+B[1]+[0]])
    elif a==0 and b==1 and len(B[0])>0 and B[0][0]>0:
        return G([U[0]+[0]+B[0]+[0],U[1]+[1]+B[1]+[0]])-(-1)^sum(U[1])*vrs[n+k]*G([U[0]+[0]+B[0]+[0],U[1]+[0]+B[1]+[0]])
    else:
        return G([U[0]+[0]+B[0]+[0],U[1]+[1]+B[1]+[0]])-(-1)^sum(U[1])*vrs[n+k]*G([U[0]+B[0]+[0,0],U[1]+B[1]+[0,0]])
def list_bicomps_n_k_ell(n,k,ell):
    if ell<max(n,k):
        return []
    if n==0:
        return [[[0]*ell,[1]*k+[0]*(ell-k)]]
    if k==0:
        return [[list(al)+[0]*(ell-len(al)),[0]*ell] for al in Compositions(n,max_length=ell)]
    return [[[r]+bc[0],[0]+bc[1]] for r in range(1,n+1) for bc in list_bicomps_n_k_ell(n-r,k,ell-1)]+\
        [[[r]+bc[0],[1]+bc[1]] for r in range(n+1) for bc in list_bicomps_n_k_ell(n-r,k-1,ell-1)]
def list_bicomps_m_ell(m,ell):
    return sum((list_bicomps_n_k_ell(m-r,r,ell) for r in range(m+1)),[])
def list_bicomps(ell):
    return sum((list_bicomps_m_ell(m,ell) for m in range(ell+1)),[])
def super_ideal(n):
    return BR(n).ideal([F(A) for A in list_bicomps(n) if sum(A[0])+sum(A[1])>0])
def list_exps_n_k_ell(n,k,ell):
    return [[list(A),list(B)] for A in IntegerVectors(n,ell) for B in IntegerVectors(k,ell,max_part=1)]
def M2_ideal(n):
    myR = 'R=QQ['+','.join('x'+str(i) for i in range(n))+','\
            +','.join('t'+str(i) for i in range(n))+','\
            +' SkewCommutative=>{'+','.join(str(i) for i in range(n,2*n))+'}];'
    macaulay2(myR)
    list_of_polynomials = [expand(F(A)) for A in list_bicomps(n) if sum(A[0])+sum(A[1])>0]
    myI = 'I=ideal('+','.join(str(p) for p in list_of_polynomials)+');'
    macaulay2(myI)
    myR = BR(n)
    inject_variables(n)
    return [myR(eval(str(p).replace("^","**"))) for p in macaulay2('gens gb I').sage()[0]]
    #macaulay2('SC=R/I;')
    #macaulay2('B = basis SC')
    #d = macaulay2('numgens source B')