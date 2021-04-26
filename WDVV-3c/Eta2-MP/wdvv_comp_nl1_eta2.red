% First-order non-local HO for hydrodynamyc-type system 
% 2021-04-20
% By JV&RV

% Computing the Schouten bracket with of the operator found in files dne3
% with itself

% Preliminaries

% The general WDVV equation expressed wrt f_3t; "gw" stands for eta 

sol_f3t := {f_3t=(f_2xt**2*gw11*gw33 - f_2xt**2*gw13**2 - f_2xt*f_x2t*gw11*gw23
  + f_2xt*f_x2t*gw12*gw13 - 3*f_2xt*gw12*gw23*gw33 + f_2xt*gw13*gw22*gw33
    + 2*f_2xt*gw13*gw23**2 - f_3x*f_x2t*gw11*gw33 + f_3x*f_x2t*gw13**2
      + f_3x*gw12*gw33**2 - f_3x*gw13*gw23*gw33 + f_x2t**2*gw11*gw22
  - f_x2t**2*gw12**2 + f_x2t*gw12*gw22*gw33 + 2*f_x2t*gw12*gw23**2
    - 3*f_x2t*gw13*gw22*gw23 - gw22**2*gw33**2 + 2*gw22*gw23**2*gw33
      - gw23**4)/
        (f_2xt*gw11*gw22 - f_2xt*gw12**2 - f_3x*gw11*gw23 +
          f_3x*gw12*gw13 + gw12*gw22*gw23 - gw13*gw22**2)}$

% Replacing variables
f_3x:=u1$
f_2xt:=u2$
f_x2t:=u3$

% Filling the matrix with values for eta case 2) in MP paper
gw11:=1;
gw12:=0;
gw13:=1;
gw22:=rho;
gw23:=0;
gw33:=mu;

% Leting mu=2 for speeding up the computation (can't be 1 - degenerate matrix;
% and 0 is another case from Dubrovin's classification)
mu:=2;

% Loading the interface to cdiff packages;
load_package cde;

% Initialization of the jet environment of the differential equation.
indep_var:={x}$
dep_var:={u1,u2,u3}$
total_order:=10$
loc_arg:={psi1,psi2,psi3}$
resname:="wdvv_comp_nl1_eta2_res.red"$

% Calling cde's main routine
cde({indep_var,dep_var,{},total_order},
  {})$

% right-hand side of the differential equation
de:={
  u2_x,
  u3_x,
  td(rhs(first(sol_f3t)),x)
    }$ 

ncomp:=length(dep_var);
nc:=ncomp;
dv1:=selectvars(0,1,dep_var,all_parametric_der)$

% Define the velocity matrix of the system

matrix av(nc,nc);
for i:=1:nc do
  for j:=1:nc do
    av(i,j):=df(part(de,i),part(dv1,j));

% Load the metric of the first-order operator
in "dne3_lho3_res.red";

% Compute the Christoffel symbols of the metric
operator gl1_op;
operator gu1_op;
for i:=1:nc do for j:=1:nc do
<<
  gl1_op(i,j):=gl1(i,j);
  gu1_op(i,j):=gu1(i,j)
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
mk_cdiffop(ham1_l,1,{3},3);
for all i,j,psi let ham1_l(i,j,psi)=
  gu1(i,j)*td(psi,x) + b(i,j)*psi;

% Coefficient matrix; syntax: c^{alpha,beta} = c(alpha,beta)
% Tail vector; syntax: w^i_\alpha = w(i,alpha)
mk_wnlop(c,w,2);
c(1,1):= rho^4;
c(2,2):= rho^3;
c(1,2):=0;
c(2,1):=0;
for i:=1:nc do w(i,1):=(for j:=1:nc sum av(i,j)*part(dv1,j));
w(1,2):=u1_x;
w(2,2):=u2_x;
w(3,2):=u3_x;

% Input for the first wnl operator
ham1:={ham1_l,c,w};

% Input for the second wnl operator
ham2:=ham1;

% The list of all distinct non-local variables to be used in the jetspace.
% Each (w^i_\alpha) (with given \alpha) gives rise to 3 distinct
% nonlocal variables \tilde{psi}^a_\alpha, a=1,2,3.
% The format of the list is:
% {nonlocal variable, tail vector, alpha}
nloc_var:={{tpsi,w,1},{tpsi,w,2}};

% Preparing the jetspace
dep_var_tot:=cde_weaklynl(indep_var,dep_var,loc_arg,nloc_var,total_order);

% The list of the two names of nonlocal variables for the two operators;
% here the two names can be the same if necessary.
nloc_arg:={{tpsi,w},{tpsi,w}};

% Computing the Schouten bracket
on time;
sb_res:=schouten_bracket_wnl(ham1,ham2,dep_var,loc_arg,nloc_arg);
off time;

off nat$
off echo$
out <<resname>>;

write sb_res;
write ";end;";
shut <<resname>>;
on echo$
on nat$

;end;

Local Variables:
mode:reduce
End: