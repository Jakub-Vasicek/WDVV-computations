% First-order non-local HO for hydrodynamyc-type system 
% 2020-04-20
% By JV&RV

% Finding the metric from the Haantjies bilinear form

% Loading the interface to cdiff packages;
load_package cde;

% Initialization of the jet environment of the differential equation.
indep_var:={x}$
dep_var:={u1,u2,u3}$
total_order:=8$
% names for results of computations
resname:="dne3_lho2_res.red"$

% Calling cde's main routine
cde({indep_var,dep_var,{},total_order},
  {})$

% right-hand side of the differential equation
de:={
u2_x, 
u3_x,
td((mu*u2^2 - mu*u1*u3 + rho*u3^2 - 1)/(rho*u2),x)
};

ncomp:=length(dep_var);
nc:=ncomp;
ford_var:=selectvars(0,1,dep_var,all_parametric_der)$

% Computing the Haantijes tensor of the matrix of velocities
% of the hydrodynamic-type system. Bogoyavlenskij approach.
in "riemann4.red"$

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
out <<resname>>;
write "matrix hmet(",nc,",",nc,");";
for i:=1:nc do for j:=1:nc do
  write "hmet(",i,",",j,"):=",hmet(i,j),"$";
write ";end;";
shut <<resname>>;
on nat$

;end;

Local Variables:
mode:reduce
End: