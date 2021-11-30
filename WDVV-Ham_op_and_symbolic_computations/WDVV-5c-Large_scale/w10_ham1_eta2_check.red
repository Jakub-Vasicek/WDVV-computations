% WDVV equation in 10 components
% Checking that Jakub's metric for 'antidiagonal eta'
% defines a third-order HO compatible with the WDVV system
% in hydrodynamic form.
% 2021-01-24

load_package cde;

% Initialization
nc:=10;

indep_var:={x}$
dep_var:=for i:=1:10 collect mkid(a,i)$;
total_order:=6$
resname:="w10_ham2_eta_check_res.red";

cde({indep_var,dep_var,{},total_order},
   {})$

% The general WDVV system
in "w10_eta2_eq_transformed.red"$
%% for i:=1:length(cons_laws_system) do
%%   set(first(part(cons_laws_system,i)),part(dep_var,i))$

cap_v:=for each el in cons_laws_system collect second el$

% Reconstructing the IIIrd order operator from the metric.
in "w10_eta2_gl3.red"$

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
tvar:=0;
for i:=1:nc do
  for h:=1:nc do
    <<
    tvar:=(
      (for j:=1:nc sum gl3(i,j)*jac_cap_v(j,h)) -
      (for j:=1:nc sum gl3(h,j)*jac_cap_v(j,i))
	);
    if tvar neq 0 then rederr "Error - metric and system not compatible!";
    >>;

% Introduce the second block of equations
for i:=1:nc do
  for j:=1:nc do
    for k:=1:nc do
    <<
      tvar:=(
	(for m:=1:nc sum c_lo(m,k,j)*jac_cap_v(m,i))
	  + (for m:=1:nc sum c_lo(m,i,k)*jac_cap_v(m,j))
	    + (for m:=1:nc sum c_lo(m,j,i)*jac_cap_v(m,k))
	      )$
      if tvar neq 0 then rederr "Error - metric and system not compatible!";
    >>;

% Introduce the second block of equations
for p:=1:nc do
  for k:=1:nc do
    for l:=1:nc do
    <<
      tvar:=(
      (for h:=1:nc sum gl3(p,h)*df(jac_cap_v(h,l),part(dep_var,k)))
	+ (for h:=1:nc sum c_lo(p,k,h)*jac_cap_v(h,l))
	  - (for h:=1:nc sum c_lo(p,h,l)*jac_cap_v(h,k))
	    );
      if tvar neq 0 then rederr "Error - metric and system not compatible!";
    >>;

pause;

% Checking the condition on Hamiltonian operator (6c) in our paper
gu3:=gl3**(-1)$
for k:=1:nc do
 for l:=1:nc do
  for m:=1:nc do
   for n:=1:nc do
  << if
      df(c_lo(m,n,k),part(dep_var,l)) + (
	for i:=1:nc sum (
	  for j:=1:nc sum ( gu3(i,j)*c_lo(i,m,l)*c_lo(j,n,k))
)) neq 0 then
      rederr "Error - not Hamiltonian!"
>>$

 ;end;
Local Variables:
mode:reduce
End:
