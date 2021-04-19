% First-order non-local HO for hydrodynamyc-type system 
% 2021-04-16
% By JV

% File ho3: using the metric that I found in ho2,
% trying to find the nonlocal tail of the operator.

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

% Filling the matrix with values for the case of flat centroaffine metric eta
gw11:=1;
gw12:=0;
gw13:=0;
gw22:=0;
gw23:=1;
gw33:=0;

% Loading the interface to cdiff packages;
load_package cde;

% Initialization of the jet environment of the differential equation.
indep_var:={x}$
dep_var:={u1,u2,u3}$
total_order:=8$
% names for results of computations
resname:="nonloc_ho3_res.red"$

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
ford_var:=selectvars(0,1,dep_var,all_parametric_der)$

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

% Loading the metric from the computation in the file ho2
in "nonloc_ho2_res.red"$

for i:=1:nc do for j:=1:nc do gu1(i,j):=gu1(i,j)$
gl1:=gu1**(-1)$

operator gl1_op,gu1_op$
for i:=1:nc do for j:=1:nc do gl1_op(i,j):=gl1(i,j)$
for i:=1:nc do for j:=1:nc do gu1_op(i,j):=gu1(i,j)$

generate_all_chr1(gl1_op,chr1_,dep_var)$
generate_all_chr2(gl1_op,gu1_op,chr1_,chr2_,dep_var)$
generate_all_chr3(gl1_op,gu1_op,chr2_,chr3_,dep_var)$

% Check that the metric fulfills the criterion on curvature
idm:=mat((1,0,0),(0,1,0),(0,0,1));
eq_curv:=for i:=1:nc join
for j:=1:nc join
  for k:=1:nc join
    for h:=1:nc collect
        riem3(gl1_op,gu1_op,chr2_,i,j,k,h,dep_var) -
         alp*(av(i,k)*av(j,h) - av(i,h)*av(j,k)) -
         bet*(av(i,k)*idm(j,h) - av(j,k)*idm(i,h) 
          - av(i,h)*idm(j,k) + av(j,h)*idm(i,k)) - 
         gam*(idm(i,k)*idm(j,h) - idm(i,h)*idm(j,k))
      $

% The constants alp=gam=0, bet=-1 fulfill the above condition 
% (and are the ONLY solution):
sol_eq_curv:=sub({
  alp=0
  ,bet=-1
  ,gam=0
  },eq_curv);
write eq_curv;
pause;

off nat$
off echo$
out <<resname>>;
write "sol_eq_curv:=",sol_eq_curv,";";
write ";end;";
shut <<resname>>;
on echo$
on nat$

;end;

Local Variables:
mode:reduce
End: