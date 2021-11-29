% WDVV equation in 3 components:
% local 3rd order Hamiltonian operator in Casimirs
% FGMN paper
% 2020-04-20
% By JV&RV


% Finding the operator using the hypothesis that coordinates in which the system is written 
% are Casimirs of the operator.
% Here we use:
% 1 - potential coordinates for the hydrodynamyc type system;
% 2 - the equations which are linear in the unknown coefficients of the Monge metric.

% File eta4: finding the operator for eta case 4) from MP paper

% Loading the interface to cdiff packages;
load_package cde;

% Initialization
indep_var:={x}$
dep_var:={u1,u2,u3}$
odd_var:={p,q,r}$
total_order:=6$

resname:="w3c_3ord_eta4_res.red"$

% Calling cde's main routine
cde({indep_var,dep_var,odd_var,total_order},
    {})$

% right-hand side of the differential equation
de:={
u2_x, 
u3_x,
td((mu*u2^2 - mu*u1*u3 + rho*u3^2 - 1)/(rho*u2),x)
};

% Number of components of the operators
nc:=length(dep_var)$
ncomp:=nc$

% Reconstructing the IIIrd order operator from the metric.

% Introduce the Monge metric in low indexes
matrix gl3(nc,nc)$
for i:=1:nc do for j:=i:nc do
<<
  gl3(i,j):=mkid(mkid(gl3_,i),j);
  if i neq j then gl3(j,i):=gl3(i,j)
>>$

% Coefficients in the Monge metric
cftel:=0$
operator cf$

% Generate the matrix of the quadratic equation that defines
% the quadratic line complex
matrix q(6,6)$
for i:=1:6 do
  for j:=i:6 do
  <<
    q(i,j):=cf(cftel:=cftel+1);
    if i neq j then q(j,i):=q(i,j)
  >>$

% Defines Lie coordinates
operator d$
d(1):=u1*db - u2*da$
d(2):=u1*dc - u3*da$
d(3):=u2*dc - u3*db$
d(4):=da$
d(5):=db$
d(6):=dc$

diffs:={da,db,dc}$

% Generating expressions with unknown coefficients cf_k
quadcpl:=for i:=1:6 sum
  for j:=1:6 sum
    d(i)*q(i,j)*d(j)$

% Giving gl3 the values
% Note: I did not know how to call an identifier gl3_ij
% so I did it in a little bit dirty way
for i:=1:nc do
  gl3(i,i):= coeffn(quadcpl,part(diffs,i),2);

for i:=1:nc do
  for j:=i+1:nc do
  begin
    gl3(i,j):=(1/2)*coeffn(coeffn(quadcpl,part(diffs,i),1),part(diffs,j),1);
    gl3(j,i):=gl3(i,j)
  end;

% Defyning the algebraic equation on g_ij (with c_ijk)

% Define c_ijk = (1/3)*(g_ki,j - g_ji,k)
operator c_lo$
for i:=1:nc do
  for j:=1:nc do
    for k:=1:nc do
      c_lo(i,j,k):=
    	(1/3)*(df(gl3(k,i),part(dep_var,j))
	  - df(gl3(j,i),part(dep_var,k)))$

% Introduce the Jacobian of the vector of fluxes of conservation laws
% Indexes are shifted because of the ordering in ford_var
ford_var:=selectvars(0,1,dep_var,all_parametric_der);
matrix cap_v(nc,nc)$
for i:=1:nc do
  for j:=1:nc do
    cap_v(i,j):=df(part(de,i),part(ford_var,j))$

% Introduce the first block of equations
% g_{ij}cap_v^j_h = cap_v^j_i g_{jh}
operator equ$
ctel:=0$
for i:=1:nc do
  for h:=1:nc do
    equ(ctel:=ctel+1):=num(
      (for j:=1:nc sum gl3(i,j)*cap_v(j,h)) -
      (for j:=1:nc sum gl3(h,j)*cap_v(j,i))
	)$

% Introduce the second block of equations
for i:=1:nc do
  for j:=1:nc do
    for k:=1:nc do
      equ(ctel:=ctel+1):=num(
      	(for m:=1:nc sum c_lo(m,k,j)*cap_v(m,i))
	  + (for m:=1:nc sum c_lo(m,i,k)*cap_v(m,j))
	    + (for m:=1:nc sum c_lo(m,j,i)*cap_v(m,k))
	      )$

% Introduce the third block of equations
for p:=1:nc do
  for k:=1:nc do
    for l:=1:nc do
      equ(ctel:=ctel+1):=num(
      	(for h:=1:nc sum gl3(p,h)*df(cap_v(h,l),part(dep_var,k)))
      	  + (for h:=1:nc sum c_lo(p,k,h)*cap_v(h,l))
	    - (for h:=1:nc sum c_lo(p,h,l)*cap_v(h,k))
	      )$

% Solving the overdetermined linear algebraic system on cf(i)
% Solve the equations
tel:=ctel$
vars:=dep_var$

initialize_equations(equ,tel,{},{cf,cftel,0},{f,0,0})$

off coefficient_check;

tel:=splitvars_opequ(equ,1,ctel,vars);

% Next command tells the solver the total number of equations obtained
% after running splitvars.

put_equations_used tel;

% This command solves the equations for the coefficients.
% Note that we have to skip the initial equations!

for i:=ctel+1:tel do integrate_equation i;

gu3:=gl3**(-1)$

operator equ2$
eqtel2:=0$
tempterm:=0$
dv1:={u1_x,u2_x,u3_x}$

for m:=1:ncomp do
 for n:=1:ncomp do
  for k:=1:ncomp do
   for l:=1:ncomp do
   <<
    tempterm:=for p:=1:ncomp sum for q:=1:ncomp sum
     gu3(p,q)*c_lo(p,m,l)*c_lo(q,n,k);
    equ2(eqtel2:=eqtel2+1):=df(c_lo(m,n,k),part(dv1,l))+tempterm
   >>$

procedure showeq();
  for i:=1:eqtel2 do if equ2 i neq 0 then write "eq. ",i," : ",equ2 i;

pause;

off nat; off echo;
off exp; on gcd;
out <<resname>>;
write "matrix gl3(",nc,",",nc,");";

for i:=1:nc do for j:=1:nc do
  write "gl3(",i,",",j,"):=",gl3(i,j),";";

write ";end;";
shut <<resname>>;

end;

