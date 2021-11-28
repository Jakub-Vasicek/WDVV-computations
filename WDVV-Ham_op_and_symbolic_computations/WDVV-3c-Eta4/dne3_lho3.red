% First-order non-local HO for hydrodynamyc-type system 
% 2020-04-20
% By JV&RV

% file lho3: attempting to solve the condition
% \nabla_k A^i_j = \nabla_j A^k_i

% Loading the interface to cdiff packages;
load_package cde;

% Initialization of the jet environment of the differential equation.
indep_var:={x}$
dep_var:={u1,u2,u3}$
total_order:=8$
% names for results of computations
resname:="dne3_lho3_res.red"$

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

% The nonlocal terms of the ansatz
operator av_con$
for i:=1:3 do av_con(i):=(for j:=1:nc sum av(i,j)*part(ford_var,j))$

% Loading pseudo-Riemannian geometry utilities
in "riemann4.red"$

% Computing the Haantijes tensor of the matrix of velocities
% of the hydrodynamic-type system. Bogoyavlenskij approach.
nc:=length(dep_var);
ford_var:=selectvars(0,1,dep_var,all_parametric_der)$

% Load the double contraction of the square of the Haantijes tensor
% - from Bogoyavlenskij

in "dne3_lho2_res.red"$

% Creating the ansatz - Ist order operator

% Defining the metric

for each el in dep_var do depend f,el$
gl1:=f*hmet$

gu1:=gl1**(-1)$
operator gl1_op,gu1_op$
for i:=1:nc do for j:=1:nc do gl1_op(i,j):=gl1(i,j)$
for i:=1:nc do for j:=1:nc do gu1_op(i,j):=gu1(i,j)$

generate_all_chr1(gl1_op,chr1_,dep_var)$
generate_all_chr2(gl1_op,gu1_op,chr1_,chr2_,dep_var)$
generate_all_chr3(gl1_op,gu1_op,chr2_,chr3_,dep_var)$

% Define the upper indices Christoffel symbols.
% Here gamma_hi(i,j,k) = \Gamma^{ij}_k
operator gamma_hi$
for i:=1:nc do for j:=1:nc do for k:=1:nc do
  gamma_hi(i,j,k):=mk_chr3(chr3_,i,j,k)$

% Introduce the contracted operator
operator gamma_hi_con$
for i:=1:nc do
 for j:=1:nc do
  gamma_hi_con(i,j):=
   <<
    templist:=for k:=1:nc collect gamma_hi(i,j,k)*mkid(part(dep_var,k),!_x)$
    templist:=part(templist,0):=plus
   >>$

% Defining the condition \nabla_k A^i_j = \nabla_j A^k_i
% The condition is equivalent to A^p_j Gamma^{si}_p = A^s_p Gamma^{pi}_j
operator ag1$
for all s,i,j let ag1(s,i,j)=(for k:=1:nc sum av(k,j)*gamma_hi(s,i,k));
operator ag2$
for all s,i,j let ag2(s,i,j)=(for k:=1:nc sum av(s,k)*gamma_hi(k,i,j));

total_eq:=
  for i:=1:nc join
    for j:=1:nc join
      for s:=1:nc collect
        ag1(s,i,j) - ag2(s,i,j)$

split_vars:=cde_difflist(all_parametric_der,dep_var)$

splitvars_total_eq:=splitvars_list(total_eq,split_vars)$

% unk contains all unknowns
unk:={f}$
% load_package trigsimp;
load_package crack;
lisp(max_gc_counter:=10000000000)$
crack_results:=crack(splitvars_total_eq,{},unk,{});

sol_unk:=second first crack_results;

gl1:=sub(sol_unk,gl1);
gu1:=sub(sol_unk,gu1);

off nat$
off echo$
off exp; on gcd;
out <<resname>>;
write "crack_results:=",crack_results,";";
write "c_3:=1/2;";
write "matrix gl1(",nc,",",nc,");";
write "matrix gu1(",nc,",",nc,");";
for i:=1:nc do for j:=1:nc do write "gl1(",i,",",j,"):=",gl1(i,j),"$";
for i:=1:nc do for j:=1:nc do write "gu1(",i,",",j,"):=",gu1(i,j),"$";
write ";end;";
shut <<resname>>;
on echo$
on nat$

;end;

Local Variables:
mode:reduce
End: