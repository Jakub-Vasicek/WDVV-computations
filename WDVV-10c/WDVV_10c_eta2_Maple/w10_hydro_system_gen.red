% WDVV equation in 10 components: local Hamiltonian operator
% Here we generate for eta2 Dubrovin's normal form
% 2021-04-19
% By JV&RV 

% Defining the WDVV equations using only the eta matrix

load_package cde$

indep_var:={t,x,y,z,w}$
dep_var:={f}$
odd_var:={p}$
total_order:=6$
resname:="w10_eta_adiag_eq.red"$

principal_der:={f_t}$
de:={0}$

% Calling cde's main routine
cde({indep_var,dep_var,odd_var,total_order},
	{principal_der,de,{},{}})$

% More initialization
nc:=length(indep_var)$
vars:=indep_var$

% The fixed metric gw in the definition of WDVV
% gwl: lower indices, gwu: upper indices
matrix gwl(nc,nc)$
% eta matrix defining the wdvv equations
gwl:=mat((1,0,0,0,1),(0,0,0,1,0),(0,0,1,0,0),(0,1,0,0,0),(1,0,0,0,0))$

gwu:=gwl**(-1)$

% Ansatz for the construction of the function (capital) F
% (not to be confused with lowercase f!), solution of the WDVV equation

cap_f:=(1/6)*gwl(1,1)*(t)**3 +
 (1/2)*(for k:=2:nc sum gwl(1,k)*part(vars,k))*(t)**2
+ (1/2)*(for k:=2:nc sum for h:=2:nc
   sum gwl(k,h)*part(vars,k)*part(vars,h))*(t)
+ f$

tot_der:=for each el in indep_var collect mkid(dd,el);

algebraic procedure ev_svf(svf_name,arg);
  svf_name(arg);

% The associativity equation
operator eqtn;
cnt:=0;
for i:=1:nc do
 for j:=1:nc do
  for k:=1:nc do
   for n:=1:nc do
    set(
 eqtn(cnt:=cnt+1),
(
for s:=1:nc sum
  for p:=1:nc sum
    ev_svf(part(tot_der,k),ev_svf(part(tot_der,i),
      ev_svf(part(tot_der,s),cap_f)))*gwu(s,p)*
  ev_svf(part(tot_der,p),ev_svf(part(tot_der,j),ev_svf(part(tot_der,n),cap_f)))
)
-
(
for s:=1:nc sum
  for p:=1:nc sum
    ev_svf(part(tot_der,j),ev_svf(part(tot_der,i),
      ev_svf(part(tot_der,s),cap_f)))*gwu(s,p)*
  ev_svf(part(tot_der,p),ev_svf(part(tot_der,k),ev_svf(part(tot_der,n),cap_f)))
    )
    )
$

tord_var:=selectvars(0,3,dep_var,all_parametric_der);
vars:=tord_var$

cftel:=2$
ctel:=1$
operator equ;
operator kappa;

% I shall filter the remaining equations for constant multiples
% Note: This relatively complicated approach has to be implemented as Reduce
% can't handle such a huge expressions well
for i:=1:cnt do
 for j:=i+1:cnt do
 	<<
 	tel:=ctel$
 	clear kappa;
 	operator kappa;

	equ(1):=kappa(1)*eqtn(i)+kappa(2)*eqtn(j)$
	initialize_equations(equ,tel,{},{kappa,cftel,0},{g,0,0})$
	off coefficient_check$
	tel:=splitvars_opequ(equ,1,ctel,vars)$
	put_equations_used tel$

	for k:=ctel+1:tel do integrate_equation k$

	if kappa(1) neq 0 and kappa(2) neq 0 and numberp(kappa(1)/kappa(2)) then
   		eqtn(j):=0$
 	>>$

% Collecting only nontrivial equations
wdvv5:={}$
for i:=1:cnt do if eqtn(i) neq 0 then wdvv5:=eqtn(i) . wdvv5$
pause;

% Constructing the compatibility system
% The algorithm:
% 1 - Find all derivatives containing x
% (which is, I guess, a chosen independent variable; what happens if I change?)
% These derivatives will be new 'letters', dependent variables for the
% compatibility system.
% 2 - Choose another independent variable, say y.
% 3 - Find all y derivatives D_y of the current dependent variable
%   as x derivatives with a two-step approach.
%   There is a unique way to find D_y as an x-derivative E_x. E can be either
%   a new letter or a symbol to be found using the wdvv-N equations. So,
%   3a - if, doing an x-derivative of one new letter one obtains D_y, then
%        E becomes that letter;
%   3b - if the previous step fails, find E inside the wdvv system.
%        NOTE: the wdvv system depends also on extra variables, those who are
%        not an x-derivative and whose x-derivative is not a y-derivative.
%        The equations containing the extra variables must be removed!

second_vars:=selectvars(0,2,dep_var,all_parametric_der)$
third_vars:=selectvars(0,3,dep_var,all_parametric_der)$
% The new 'letters' of the system
third_xvars:=for each el in second_vars collect td(el,x)$
% The complement of third_xvars
third_noxvars:=cde_difflist(third_vars,third_xvars)$
% The y derivatives of all 'letters', which will be
% the lhs of the compatibility system (densities)
fourth_yxvars:=for each el in third_xvars collect {el,td(el,y)}$

% Try to find y-ders as x-ders of 'letter' or 'expression'
% in wdvv.

% This will contain the fluxes
conserved_vector:={}$

xvar:={};
for each el in fourth_yxvars do
  for each ell in third_xvars do
    if td(ell,x)=second(el) then
    <<
      xvar:=ell . xvar;
      conserved_vector:={first(el),ell} . conserved_vector
    >>;

noxvar:={};
for each el in fourth_yxvars do
  for each ell in third_noxvars do
    if td(ell,x)=second(el) then
    <<
      noxvar:=ell . noxvar;
      conserved_vector:={first(el),ell} . conserved_vector
    >>;
othervar:=cde_difflist(third_vars,append(third_xvars,noxvar))$

sys_y:={}$
for each el in wdvv5 do
  if cde_freeofl(el,othervar) then sys_y:=el . sys_y;

sol_sys_y:=first solve(sys_y,noxvar)$

cons_laws_system:=(conserved_vector where sol_sys_y);
cons_laws_system:=reverse(cons_laws_system);

off echo$
off nat$
out <<resname>>$

write "% WDVV equations for eta2";
write "The_WDVV_system:=", wdvv5;
write "cons_laws_system:=", cons_laws_system;

write ";end;";

shut <<resname>>;

;end;

Local Variables:
mode:reduce
End:
