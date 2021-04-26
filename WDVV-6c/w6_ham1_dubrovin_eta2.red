% WDVV equation in 6 components:
% local 3rd order Hamiltonian operator in Casimirs
% 2021-04-20
% By JV&RV

% File ham1: finding the operator using the hypothesis that
% coordinates in which the system is written are Casimirs of the operator.
% Here I use:
% 1 - potential coordinates for the hydrodynamyc type system;
% 2 - the equations which are linear in the unknown coefficients
% of the Monge metric.

load_package cde;

% Initialization

indep_var:={t,x}$
dep_var:={a,b,c,d,ee,f}$
odd_var:={p1,p2,p3,p4,p5,p6}$
total_order:=6$
resname:="w6_ham1_dubrovin_eta2_res.red"$

% left-hand side of the differential equation
principal_der:={a_t,b_t,c_t,d_t,ee_t,f_t}$
% right-hand side of the differential equation
% de:={b_x , c_x , rhs(first(sol_f3t))}$
de:={b_x , c_x , 0}$
% same constructions for odd coordinates;

principal_odd:={p1_t,p2_t,p3_t,p4_t,p5_t,p6_t}$
de_odd:={0, 0, 0, 0, 0, 0}$

% Calling cde's main routine
cde({indep_var,dep_var,odd_var,total_order},
   {{principal_der,de,principal_odd,de_odd}})$

% Number of components of the operators
ncomp:=length(dep_var)$
nc:=ncomp$

% The general WDVV system
in "w6_dubrovin_eta2_res.red"$
for i:=1:length(cons_laws_system) do
  set(first(part(cons_laws_system,i)),part(dep_var,i))$

cap_v:=for each el in cons_laws_system collect second el$

% Reconstructing the IIIrd order operator from the metric.

% Must define one arbitrary Monge metric (as a matrix),
% then rename it as 'gl3'.

% Number of components in projective space
ncp:=nc+1$

% Number of Plucker coordinates
npl:=(ncp*(ncp-1))/2$

matrix gl3(nc,nc)$

operator cf$
cftel:=0$

% Generate the matrix of the quadratic equation
% that defines the quadratic line complex
matrix q(npl,npl)$
for i:=1:npl do
for j:=i:npl do
<<
 q(i,j):=cf(cftel:=cftel+1)$
 if i neq j then q(j,i):=q(i,j)$
>>$

operator pc$
proj_coord:=p0 . dep_var$

plucker_coord:=for i:=ncp step -1 until 1 join for j:=1:i-1 collect pc(i,j)$
for i:=ncp step -1 until 1 do for j:=1:i-1 do pc(j,i):= - pc(i,j)$

lie_coord:=for each el in plucker_coord collect
 part(proj_coord,part(el,1))*mkid(d,part(proj_coord,part(el,2)))
  - part(proj_coord,part(el,2))*mkid(d,part(proj_coord,part(el,1)))$

quadcpl:=for i:=1:npl sum
          for j:=1:npl sum
           part(lie_coord,i)*q(i,j)*part(lie_coord,j)$

% The projection on the affine space
p0:=1$
dp0:=0$
affine_diffs:=for each el in dep_var collect mkid(d,el)$

% Fill the matrix of the metric with its coefficients
for i:=1:nc do gl3(i,i):=coeffn(quadcpl,part(affine_diffs,i),2)$
for i:=1:nc do
  for j:=i+1:nc do
  <<
    gl3(i,j):=(1/2)*coeffn(coeffn(quadcpl,
      part(affine_diffs,i),1),part(affine_diffs,j),1);
    gl3(j,i):=gl3(i,j)
  >>$

% Define c_ijk = (1/3)*(g_ki,j - g_ji,k)
operator c_lo$
for i:=1:nc do
 for j:=1:nc do
  for k:=1:nc do
  <<
   c_lo(i,j,k):=
    (1/3)*(df(gl3(k,i),part(dep_var,j)) - df(gl3(j,i),part(dep_var,k)))$
  >>$

% Introduce the Jacobian of the vector of fluxes of conservation laws
matrix jac_cap_v(nc,nc)$
for i:=1:nc do
  for j:=1:nc do
    jac_cap_v(i,j):=df(part(cap_v,i),part(dep_var,j))$

% Introduce the first block of equations
% g_{ij}cap_v^j_h = cap_v^j_i g_{jh}
operator equ$
ctel:=0$
for i:=1:nc do
  for h:=1:nc do
    equ(ctel:=ctel+1):=num(
      (for j:=1:nc sum gl3(i,j)*jac_cap_v(j,h)) -
      (for j:=1:nc sum gl3(h,j)*jac_cap_v(j,i))
	)$

% Introduce the second block of equations
for i:=1:nc do
  for j:=1:nc do
    for k:=1:nc do
      equ(ctel:=ctel+1):=num(
        (for m:=1:nc sum c_lo(m,k,j)*jac_cap_v(m,i))
          + (for m:=1:nc sum c_lo(m,i,k)*jac_cap_v(m,j))
            + (for m:=1:nc sum c_lo(m,j,i)*jac_cap_v(m,k))
              )$

% Introduce the second block of equations
for p:=1:nc do
  for k:=1:nc do
    for l:=1:nc do
      equ(ctel:=ctel+1):=num(
      (for h:=1:nc sum gl3(p,h)*df(jac_cap_v(h,l),part(dep_var,k)))
      	+ (for h:=1:nc sum c_lo(p,k,h)*jac_cap_v(h,l))
	  - (for h:=1:nc sum c_lo(p,h,l)*jac_cap_v(h,k))
	    )$

% Very long computation ahead f(15000s) 
pause;

% Solve the equations
tel:=ctel$
vars:=dep_var$

initialize_equations(equ,tel,{},{cf,cftel,0},{f,0,0})$

% off coefficient_check;

tel:=splitvars_opequ(equ,1,tel,vars)$

% Next command tells the solver the total number of equations obtained
% after running splitvars.

put_equations_used tel;

% This command solves the equations for the coefficients.
% Note that we have to skip the initial equations!

for i:=ctel+1:tel do integrate_equation i;

% Output for the metric g
off echo$ off nat$

out <<resname>>$

write "% Metric g_{i,j}:";

write "matrix ggl3(", ncomp, ",", ncomp, ")$";
for i:=1:nc do
  for j:=1:nc do
    write "ggl3(",i,",",j,") =", gl3(i,j),"$";

write ";end;";

shut <<resname>>;
on nat; on echo;

gu3:=gl3**(-1)$

% Checking the condition on Hamiltonian operator
for k:=1:ncomp do 
 for l:=1:ncomp do 
  for m:=1:ncomp do 
   for n:=1:ncomp do 
  << if 
      df(c_lo(m,n,k),part(dep_var,l)) + (
        for i:=1:ncomp sum ( 
          for j:=1:ncomp sum ( gu3(i,j)*c_lo(i,m,l)*c_lo(j,n,k))
)) neq 0 then
      rederr "Error - not Hamiltonian!"
>>$

;end;
Local Variables:
mode:reduce
End:
