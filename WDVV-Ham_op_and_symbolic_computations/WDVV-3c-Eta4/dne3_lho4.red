% First-order non-local HO for hydrodynamyc-type system 
% 2020-04-20
% By JV&RV

% File lho4: using the metric that I found in lho3,
% trying to find the nonlocal tail of the operator.

% Loading the interface to cdiff packages;
load_package cde;

% Initialization of the jet environment of the differential equation.
indep_var:={x}$
dep_var:={u1,u2,u3}$
total_order:=8$
% names for results of computations
resname:="dne3_lho4_res.red"$

% Calling cde's main routine
cde({indep_var,dep_var,{},total_order},
  {})$

% right-hand side of the differential equation
de:={
u2_x, 
u3_x,
td((mu*u2^2 - mu*u1*u3 + rho*u3^2 - 1)/(rho*u2),x)
};

nc:=length(dep_var)$
ford_var:={u1_x,u2_x,u3_x}$

% Define the velocity matrix of the system

matrix av(nc,nc);
for i:=1:nc do
  for j:=1:nc do
    av(i,j):=df(part(de,i),part(ford_var,j));

% A vector which is useful for constructing the ansatz
operator av_con$
for i:=1:3 do av_con(i):=(for j:=1:nc sum av(i,j)*part(ford_var,j))$

% Loading pseudo-Riemannian geometry utilities
in "riemann4.red"$

% Loading the metric from the computation in the file lho3
in "dne3_lho3_res.red"$

for i:=1:nc do for j:=1:nc do gu1(i,j):=2*c_3*gu1(i,j)$
gl1:=gu1**(-1)$

operator gl1_op,gu1_op$
for i:=1:nc do for j:=1:nc do gl1_op(i,j):=gl1(i,j)$
for i:=1:nc do for j:=1:nc do gu1_op(i,j):=gu1(i,j)$

generate_all_chr1(gl1_op,chr1_,dep_var)$
generate_all_chr2(gl1_op,gu1_op,chr1_,chr2_,dep_var)$
generate_all_chr3(gl1_op,gu1_op,chr2_,chr3_,dep_var)$

% Check that the metric fulfills the criterion
% R^{ij}_kh = alp*(A^i_k*A^j_h - A^j_k*A^i_h) -
%             bet*(A^i_k*delta^j_h-A^j_k*delta^i_h-
%                  A^i_h*delta^j_k - A^j_h*delta^i_k) -
%             gam*(delta^i_k*delta^j_h - delta^j_k*delta^i_h)
idm:=mat((1,0,0),(0,1,0),(0,0,1));
eq_curv:=for i:=1:nc join
for j:=1:nc join
  for k:=1:nc join
    for h:=1:nc collect
    riem3(gl1_op,gu1_op,chr2_,i,j,k,h,dep_var) -
  alp*(av(i,k)*av(j,h) - av(i,h)*av(j,k)) -
      bet*(av(i,k)*idm(j,h) - av(j,k)*idm(i,h) - 
        av(i,h)*idm(j,k) + av(j,h)*idm(i,k)) -
    gam*(idm(i,k)*idm(j,h) - idm(i,h)*idm(j,k))
      $

% The constants alp=mu, bet=0 and gamma=rho fulfill the above condition 
% (and are the ONLY solution)
A:=sub({
  alp=mu,
  bet=0
  ,gam=rho
  },eq_curv);
write eq_curv;

% Testing for all possible combinations of rho and mu
sub({mu=1,rho=1},A);
sub({mu=-1,rho=1},A);
sub({mu=1,rho=-1},A);
sub({mu=-1,rho=-1},A);

pause;

off nat$
off echo$
out <<resname>>;
write "eq_curv:=",eq_curv,";";
write ";end;";
shut <<resname>>;
on echo$
on nat$

;end;

Local Variables:
mode:reduce
End: