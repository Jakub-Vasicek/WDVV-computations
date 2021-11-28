% WDVV equation in 10 components: local Hamiltonian operator
% 2016-02-14

% Defining the WDVV equations using
% as eta the antidiagonal identity matrix.

load_package cde$

indep_var:={t,x,y,z,w}$
dep_var:={f}$
odd_var:={p}$
total_order:=6$
resname:="w10_eta1_res.red"$

% Calling cde's main routine
cde({indep_var,dep_var,odd_var,total_order},{})$

% More initialization
nc:=length(indep_var)$
vars:=indep_var$

% The fixed metric gw in the definition of WDVV
% gwl: lower indices, gwu: upper indices
matrix gwl(nc,nc)$
% This is Dubrovin's matrix
gwl:=mat((1,0,0,0,0),(0,0,0,0,1),(0,0,0,1,0),(0,0,1,0,0),(0,1,0,0,0))$
% Code for a generic metric
%% for i:=1:nc do for j:=i:nc do
%% <<
%%   gwl(i,j):=mkid(mkid(gw,i),j);
%%   if i neq j then gwl(j,i):=gwl(i,j)
%% >>$

gwu:=gwl**(-1)$

% Ansatz for the construction of the function (capital) F
% (not to be confused with lowercase f!), solution of the WDVV equation

cap_f:=(1/6)*gwl(1,1)*(t)**3 +
 (1/2)*(for k:=2:nc sum gwl(1,k)*part(vars,k))*(t**2)
+ (1/2)*(for k:=2:nc sum for h:=2:nc
   sum gwl(k,h)*part(vars,k)*part(vars,h))*t
+ f$

tot_der:=for each el in indep_var collect mkid(dd,el);

algebraic procedure ev_svf(svf_name,arg);
  svf_name(arg);

% The associativity equation
operator equ;
cnt:=0;
for i:=1:nc do
 for j:=1:nc do
  for k:=1:nc do
   for n:=1:nc do
    set(
 equ(cnt:=cnt+1),
(
for s:=1:nc sum
  for p:=1:nc sum
    ev_svf(part(tot_der,k),ev_svf(part(tot_der,i),
      ev_svf(part(tot_der,s),cap_f)))*gwu(s,p)*
  ev_svf(part(tot_der,p),ev_svf(part(tot_der,j),ev_svf(part(tot_der,n),cap_f)))
%    td(cap_f,part(indep_var,k),part(indep_var,i),part(indep_var,s))*gwu(s,p)*
%  td(cap_f,part(indep_var,p),part(indep_var,j),part(indep_var,n))
)
-
(
for s:=1:nc sum
  for p:=1:nc sum
    ev_svf(part(tot_der,j),ev_svf(part(tot_der,i),
      ev_svf(part(tot_der,s),cap_f)))*gwu(s,p)*
  ev_svf(part(tot_der,p),ev_svf(part(tot_der,k),ev_svf(part(tot_der,n),cap_f)))
%    td(cap_f,part(indep_var,j),part(indep_var,i),part(indep_var,s))
%      *gwu(s,p)*
%	td(cap_f,part(indep_var,p),part(indep_var,k),part(indep_var,n)))
    )
      )
$

% I shall filter the remaining equations for constant multiples
for i:=1:cnt do
 for j:=i+1:cnt do
  if equ(i) neq 0 and equ(j) neq 0 and numberp(equ(i)/equ(j)) then
   equ(j):=0$

% Collecting only nontrivial equations
wdvv5:={}$
for i:=1:cnt do if equ(i) neq 0 then wdvv5:=equ(i) . wdvv5$

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

write "cons_laws_system:=",cons_laws_system;

write ";end;";

shut <<resname>>;

;end;

Local Variables:
mode:reduce
End:
