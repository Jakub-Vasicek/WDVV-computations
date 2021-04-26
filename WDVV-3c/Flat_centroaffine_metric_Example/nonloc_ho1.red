% First-order non-local HO for hydrodynamyc-type system 
% 2021-04-18
% By JV

% File ho1: finding the metric from the Haantjies bilinear form

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
resname:="nonloc_ho1_res.red"$

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

% Computing the Haantijes tensor of the matrix of velocities
% of the hydrodynamic-type system. Bogoyavlenskij approach.
in "riemann4.red"$

ford_var:=selectvars(0,1,dep_var,all_parametric_der)$

matrix av(nc,nc);
for i:=1:nc do
  for j:=1:nc do
    av(i,j):=df(part(de,i),part(ford_var,j));

operator avt;
for i:=1:ncomp do for j:=1:ncomp do
  avt(i,j):=av(i,j)$
generate_all_nt(avt,dep_var);
generate_all_ht(avt,dep_var);

temphtc:={}$
matrix hmet(nc,nc);
for i:=1:nc do
  for j:=1:nc do
    hmet(i,j):=
    <<
      temphtc:=for k:=1:nc join for h:=1:nc collect
	riemann_list2ids({ht_,k,i,h})*riemann_list2ids({ht_,h,j,k});
      part(temphtc,0):=plus
    >>;

% Trying the symmetry condition with respect to the velocity matrix, OK!
for i:=1:nc do for j:=i+1:nc do
<<
  templhs:=(for h:=1:nc sum hmet(i,h)*av(h,j));
  temprhs:=(for h:=1:nc sum hmet(j,h)*av(h,i));
  write templhs - temprhs
>>;

% Saving the Haantijes metric
off nat$
off echo$
%off exp; on gcd; on ezgcd;
out <<resname>>;
write "matrix hmet(",nc,",",nc,");";
for i:=1:nc do for j:=1:nc do
  write "hmet(",i,",",j,"):=",hmet(i,j),"$";
write ";end;";
shut <<resname>>;
%off ezgcd; off gcd; on exp;
on echo$
on nat$

;end;

Local Variables:
mode:reduce
End: