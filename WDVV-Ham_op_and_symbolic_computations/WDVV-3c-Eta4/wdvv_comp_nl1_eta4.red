% First-order HO for hydrodynamyc-type system compatible with g^3 for 
% the case eta4
% 2020-04-20
% By JV&RV

% Loading the interface to cdiff packages;
load_package cde;

% Initialization of the jet environment of the differential equation.
indep_var:={x}$
dep_var_equ:={u1,u2,u3}$
total_order:=10$
loc_arg:={psi1,psi2,psi3}$
% names for output of the state of cde and results of computations
resname:="wdvv_comp_nl1_eta4_res.red"$

% Calling cde's main routine
cde({indep_var,dep_var_equ,{},total_order},
  {})$

% right-hand side of the differential equation
de:={
u2_x, 
u3_x,
td((mu*u2^2 - mu*u1*u3 + rho*u3^2 - 1)/(rho*u2),x)
};

nc:=length(dep_var_equ)$
dv1:={u1_x,u2_x,u3_x}$

% Define the velocity matrix of the system

matrix av(nc,nc);
for i:=1:nc do
  for j:=1:nc do
    av(i,j):=df(part(de,i),part(dv1,j));

% Load the metric of the first-order operator
in "dne3_lho3_res.red";
gu1:=gl1**(-1);

% Compute the Christoffel symbols of the metric
operator gl1_op;
operator gu1_op;
for i:=1:nc do for j:=1:nc do
<<
  gl1_op(i,j):=gl1(i,j);
  gu1_op(i,j):=gu1(i,j)
>>$

in "riemann4.red"$
vars:=dep_var_equ;
generate_all_chr1(gl1_op,chr1_,vars);
generate_all_chr2(gl1_op,gu1_op,chr1_,chr2_,vars);
generate_all_chr3(gl1_op,gu1_op,chr2_,chr3_,vars);

operator b;
for i:=1:nc do for j:=1:nc do
  b(i,j):=for k:=1:nc sum mk_chr3(chr3_,i,j,k)*part(dv1,k);

% Defining the local part of the operator
mk_cdiffop(ham1_l,1,{3},3);
for all i,j,psi let ham1_l(i,j,psi)=
  gu1(i,j)*td(psi,x) + b(i,j)*psi;

% Coefficient matrix; syntax: c^{alpha,beta} = c(alpha,beta)
% Tail vector; syntax: w^i_\alpha = w(i,alpha)
mk_wnlop(c,w,2);
c(1,1):= mu;
c(2,2):= rho;
c(1,2):=0;
c(2,1):=0;
for i:=1:nc do w(i,1):=(for j:=1:nc sum av(i,j)*part(dv1,j));
w(1,2):=u1_x;
w(2,2):=u2_x;
w(3,2):=u3_x;

% Checked for all possible combiantion, REDUCE cannot simplify 
% the terms with arbitrary mu or rho
% mu:=1;
% rho:=1;

% Input for the first wnl operator
ham1:={ham1_l,c,w};

% Input for the second wnl operator
ham2:=ham1;

% The list of all distinguished tail vectors involved in the calculation.
% Each (w^i_\alpha) (with given \alpha) gives rise to 3 nonlocal variables
% \tilde{psi}^a_\alpha, a=1,2,3.
nloc_var:={{tpsi,w,1},{tpsi,w,2}};

% Preparing the jetspace
dep_var_tot:=cde_weaklynl(indep_var,dep_var_equ,loc_arg,nloc_var,total_order);

% The list of the two names of nonlocal variables for the two operators;
% here the two names can be the same if necessary.
nloc_arg:={{tpsi,w},{tpsi,w}};

% Computing the Schouten bracket
on time;
sb_res:=schouten_bracket_wnl(ham1,ham2,dep_var_equ,loc_arg,nloc_arg);
off time;
off exp; on gcd;

% Testing for all possible combinations of rho and mu
A:=sub({mu=1,rho=1},sb_res);
B:=sub({mu=-1,rho=1},sb_res);
C:=sub({mu=1,rho=-1},sb_res);
D:=sub({mu=-1,rho=-1},sb_res);

pause;

off nat$
off echo$
out <<resname>>;

write A;
write B;
write C;
write D;

write ";end;";
shut <<resname>>;
on echo$
on nat$

;end;

Local Variables:
mode:reduce
End: