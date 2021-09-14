% First-order non-local HO for hydrodynamyc-type system 
% 2021-01-20
% By JV&RV

% file lho3: attempting to solve the condition
% \nabla_k A^i_j = \nabla_j A^k_i

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

% Filling the matrix with values for eta case 2) for Dubrovin's classification
gw11:=mu;
gw12:=0;
gw13:=1;
gw22:=1;
gw23:=0;
gw33:=0;

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
  td(rhs(first(sol_f3t)),x)
    }$ 

ncomp:=length(dep_var);
nc:=ncomp;
ford_var:=selectvars(0,1,dep_var,all_parametric_der)$

% Computing the Haantijes tensor of the matrix of velocities
% of the hydrodynamic-type system. Bogoyavlenskij approach.
in "riemann4.red"$

% Define the velocity matrix of the system
matrix av(nc,nc);
for i:=1:nc do
  for j:=1:nc do
    av(i,j):=df(part(de,i),part(ford_var,j));

% The nonlocal terms of the ansatz
operator av_con$
for i:=1:3 do av_con(i):=(for j:=1:nc sum av(i,j)*part(ford_var,j))$

% Computing the Haantijes tensor of the matrix of velocities
% of the hydrodynamic-type system. Bogoyavlenskij approach.
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