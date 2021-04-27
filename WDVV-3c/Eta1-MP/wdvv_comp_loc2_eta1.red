% WDVV equation in 3 components:
% Compatibility test of local 1st and 3rd order Hamiltonian operators
% For a case 1) from M-P paper, where there is a known local 
% first-order Hamiltonian operator
% 2021-04-19 by JV&RV

% Preliminaries 

% Loading the cde package
load_package cde;

% Initialization
indep_var:={x}$
dep_var:={u1,u2,u3}$
odd_var:={p,q,r}$
total_order:=10$
resfile:="w3c_compat_local_eta1_res.red"$

% Calling cde's main routine
cde({indep_var,dep_var,odd_var,total_order},
  {})$

% Number of components of the operators
ncomp:=length(dep_var)$
nc:=ncomp$
dv1:={u1_x,u2_x,u3_x}$

% Define the leading term of the first-order operator
% Metric g^{ij}_1
matrix gu_1(nc,nc)$

% The metric found by M-P for case 1)
gu_1(1,1):= 3/2$
gu_1(1,2):= -u1/2$
gu_1(1,3):= rho*mu/2-u2$
gu_1(2,2):= rho*mu/2-u2$
gu_1(2,3):= -3*u3/2$
gu_1(3,3):= 2*u1*u3+2*rho*mu*u2-2*u2**2-(rho*mu)**2/2$
gu_1(3,1):= gu_1(1,3)$
gu_1(2,1):= gu_1(1,2)$
gu_1(3,2):= gu_1(2,3)$

gl_1:=gu_1**(-1)$

% Compute the Christoffel symbols of the metric
operator gl1_op;
operator gu1_op;
for i:=1:nc do for j:=1:nc do
<<
  gl1_op(i,j):=gl_1(i,j);
  gu1_op(i,j):=gu_1(i,j)
>>$

in "riemann4.red"$
vars:=dep_var;
generate_all_chr1(gl1_op,chr1_,vars);
generate_all_chr2(gl1_op,gu1_op,chr1_,chr2_,vars);
generate_all_chr3(gl1_op,gu1_op,chr2_,chr3_,vars);

operator b;
for i:=1:nc do for j:=1:nc do
  b(i,j):=for k:=1:nc sum mk_chr3(chr3_,i,j,k)*part(dv1,k);

% Defining the local part of the operator
mk_cdiffop(ham1,1,{3},3);
for all i,j,psi let ham1(i,j,psi)=
  gu_1(i,j)*td(psi,x) + b(i,j)*psi;

% Reconstruction of the third order operator.
in "w3c_3ord_eta1_res.red";
gu3:=gl3**(-1)$

% Define c_ijk = (1/3)*(g_ki,j - g_ji,k)
operator c_lo$
for i:=1:nc do
 for j:=1:nc do
  for k:=1:nc do
   c_lo(i,j,k):=
    (1/3)*(df(gl3(i,k),part(dep_var,j)) 
    - df(gl3(i,j),part(dep_var,k)))$

% Define c^ij_k=c_hi(i,j,k) using the formula
% g^ni*g^mj*c_mnk = c^ij_k
templist:={}$
operator c_hi$
for i:=1:nc do
 for j:=1:nc do
  for k:=1:nc do
   c_hi(i,j,k):=
    <<
     templist:=
      for m:=1:nc join
       for n:=1:nc collect
        gu3(n,i)*gu3(m,j)*c_lo(m,n,k)$
     templist:=part(templist,0):=plus
    >>$

% Introduce the contraction of c_ijk 
operator c_hi_con$
for i:=1:nc do
 for j:=1:nc do
  c_hi_con(i,j):=
   <<
    templist:=for k:=1:nc collect c_hi(i,j,k)*mkid(part(dep_var,k),!_x)$
    templist:=part(templist,0):=plus
   >>$

% The third-order Hamiltonian operator aa3
mk_cdiffop(ham2,1,{nc},nc)$
for all i,j,psi let ham2(i,j,psi) =
td(
gu3(i,j)*td(psi,x,2)+c_hi_con(i,j)*td(psi,x)
,x)$

% Convert operators into bivectors
conv_cdiff2superfun(ham1,sym1)$
conv_cdiff2superfun(ham2,sym3)$
conv_genfun2biv(sym1,biv1)$
conv_genfun2biv(sym3,biv3)$

% Compute the Schouten bracket of the first-order operator with itself for checking
schouten_bracket(biv1,biv1,sb11);
euler_df(sb11(1));

% Compute the Schouten bracket of the third-order operator with itself for checking
schouten_bracket(biv3,biv3,sb33);
euler_df(sb33(1));

% Finally compute the Schouten bracket of two Hamiltonian operators
schouten_bracket(biv1,biv3,sb13);
sb_res:=euler_df(sb13(1))$

% The above is not 0 for any real constant lambda, only for lambda^2=1
A:=sub({rho=1},sb_res);
B:=sub({rho=-1},sb_res);

off nat$
off echo$
out <<resfile>>;

write A;
write B;
write ";end;";
shut <<resfile>>;
on echo$
on nat$

;end;
