%% Formulae for Riemannian geometry starting from the metric gmat
%% inserted as a matrix
% 2013-01-10
% Changes on 137,138,142,143 (sign of the Riemann curvature)

% In this library file `gmat' stands for an operator containing the
% entries of the metric with lower indexes

symbolic operator getmatel;
symbolic procedure getmatel(mat_d,i,j);
% MacCallum-Wright p. 245
% handling of local matrices
nth(nth(cdr mat_d,i),j);

symbolic operator setmatel;
symbolic procedure setmatel(mat_d,i,j,val);
% MacCallum-Wright p. 245
% handling of local matrices
<<
rplaca(pnth(nth(cdr mat_d,i),j),val);
mat_d
>>;

symbolic procedure riemann_list2ids0 l;
% Comes from the procedure list_to_ids in genpurfn.red, assist package,
% by H. Caprasse.
   if atom l then rederr "argument for riemann_list2ids must be a list"
   else intern compress for each i in l join explode i;

symbolic procedure riemann_list2ids l;
  riemann_list2ids0(cdr l);

symbolic operator riemann_list2ids;

procedure chr1(gmat,i,j,k,vars);
% Christoffel symbols of the first kind \Gamma_{ijk}
   (1/2)*(df(gmat(i,j),part(vars,k))+df(gmat(i,k),part(vars,j))
      -df(gmat(j,k),part(vars,i)));

procedure mk_chr1(chr1_name,i,j,k);
% Generate a symbol from the table of all Christoffel symbols
   riemann_list2ids({chr1_name,i,j,k});

procedure generate_all_chr1(gmat,chr1_name,vars);
  % Generate all Christoffel symbols of type 1,
  % denoted with the symbol 'chr1_nameijk'
begin scalar n_vars,list_done;
   n_vars:=length(vars);
   list_done:={};
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      if not ({i,j,k} member list_done) then
      <<
       set(mk_chr1(chr1_name,i,j,k),chr1(gmat,i,j,k,vars));
       list_done:={i,j,k} . list_done
      >>;
end;

procedure nabla(gmat,chr1_name,i,j,k,vars);
% Verification: \nabla am =0
   df(gmat(i,j),part(vars,k))
      -mk_chr1(chr1_name,i,j,k)-mk_chr1(chr1_name,j,i,k);

operator chr2_aff$

procedure nabla_aff(chr2_aff,i,j,k,gmat,vars);
% Computation of \nabla[chr2_aff]; note that chr2_aff must be given,
  % possibly through an operator.
  begin
    scalar l_vars,tempterm1,tempterm2;
    l_vars:=length(vars);
    tempterm1:=for s:=1:l_vars collect gmat(i,s)*chr2_aff(s,j,k);
    tempterm1:=part(tempterm1,0):=plus;
    tempterm2:=for s:=1:l_vars collect gmat(j,s)*chr2_aff(s,i,k);
   return df(gmat(i,j),part(vars,k)) - tempterm1 - tempterm2
  end;

procedure check_nabla(gmat,chr1_name,vars);
  % Checking that nabla is a metric connection
  % Can be issued only after generating all Christoffe symbols of type 1.
begin
n_gmat:=length(vars);
return
for i:=1:n_gmat do
<<
for j:=1:n_gmat do
<<
for k:=1:n_gmat do
<<
   if nabla(gmat,chr1_name,i,j,k,vars) neq 0 then
      rederr "Error! Wrong Christoffel symbols."
>>
>>
>>
end;

procedure chr2(gmat,inv_gmat,chr1_name,i,j,k,vars);
% Christoffel symbols of the second kind of gmat, \Gamma^i_{jk}
% inv_gmat should be an operator containing the inverse of gmat
begin
  scalar n_gmat,tempchr2;
  n_gmat:=length(vars);
  tempchr2:={};
  return
  <<
    tempchr2:=for s:=1:n_gmat collect inv_gmat(i,s)*mk_chr1(chr1_name,s,j,k);
    part(tempchr2,0):=plus
  >>
end;

procedure mk_chr2(chr2_name,i,j,k);
% Generate a symbol from the table of all Christoffel symbols
   riemann_list2ids({chr2_name,i,j,k});

procedure generate_all_chr2(gmat,inv_gmat,chr1_name,chr2_name,vars);
% Generate all Christoffel symbols of type 2, denoted with 'chr2ijk'
begin scalar n_vars,list_done;
   list_done:={};
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      if not ({i,j,k} member list_done) then
      <<
       set(mk_chr2(chr2_name,i,j,k),chr2(gmat,inv_gmat,chr1_name,i,j,k,vars));
       list_done:={i,j,k} . list_done
      >>;
end;

procedure riem2(gmat,chr2_name,l,i,j,k,vars);
% Curvature of the Riemannian connection of gmat, R^l_{ijk}
begin scalar n_gmat,tempriem2;
  tempriem2:={};
   n_gmat:=length(vars);
   return
     - df(mk_chr2(chr2_name,l,i,k),part(vars,j))
      + df(mk_chr2(chr2_name,l,i,j),part(vars,k))+
      <<
	tempriem2:=
	  for s:=1:n_gmat collect
 	    - mk_chr2(chr2_name,l,j,s)*mk_chr2(chr2_name,s,i,k)
         + mk_chr2(chr2_name,l,k,s)*mk_chr2(chr2_name,s,i,j);
	part(tempriem2,0):=plus
      >>
end;

procedure riem2_aff(chr2_aff,l,i,j,k,vars);
% Curvature of an affine connection with Christoffel symbols
% chr2_aff(i,j,k) (declared as an operator before), R^l_{ijk}
begin
  scalar n_vars,tempriem2_aff;
  n_vars:=length(vars);
  tempriem2_aff:={};
  return df(chr2_aff(l,i,k),part(vars,j))
      -df(chr2_aff(l,i,j),part(vars,k))+
      <<
	tempriem2_aff:=for s:=1:n_vars collect
	  (chr2_aff(l,j,s)*chr2_aff(s,i,k)
      	  -chr2_aff(l,k,s)*chr2_aff(s,i,j));
	part(tempriem2_aff,0):=plus
      >>
end;

procedure riem1(gmat,chr2_name,l,i,j,k,vars);
% Curvature of the Riemannian connection of gmat, R_{lijk}
begin scalar n_gmat,tempriem1;
  n_gmat:=length(vars);
  tempriem1:={};
  return
  <<
    tempriem1:=for s:=1:n_gmat collect
      gmat(l,s)*riem2(gmat,chr2_name,s,i,j,k,vars);
    part(tempriem1,0):=plus
  >>
end;

procedure check_riem1(gmat,chr2_name,vars);
begin scalar n_gmat;
n_gmat:=length(vars);
return
 for i:=1:n_gmat do
  for k:=1:n_gmat do
   for l:=1:n_gmat do
    for m:=1:n_gmat do
    <<
   if
     (riem1(gmat,chr2_name,i,k,l,m,vars)
       -riem1(gmat,chr2_name,l,m,i,k,vars) neq 0) or
     (riem1(gmat,chr2_name,i,k,l,m,vars)
       +riem1(gmat,chr2_name,k,i,l,m,vars) neq 0) or
     (riem1(gmat,chr2_name,i,k,l,m,vars)
       +riem1(gmat,chr2_name,i,k,m,l,vars) neq 0) or
     (riem1(gmat,chr2_name,i,k,l,m,vars)
       +riem1(gmat,chr2_name,i,m,k,l,vars)
         +riem1(gmat,chr2_name,i,l,m,k,vars) neq 0)
   then
      write "Error! Wrong Riemannian curvature:",
       " i:=",i," k:=",k," l:=",l," m:=", m
   >>
end;

procedure ricci(gmat,chr2_name,i,j,vars);
% Ricci tensor of the Riemannian connection of gmat, R_{ij}
begin
  scalar n_gmat,tempricci;
  n_gmat:=length(vars);
  tempricci:={};
  return
  <<
    tempricci:=for s:=1:n_gmat collect riem2(gmat,chr2_name,s,i,s,j,vars);
    part(tempricci,0):=plus
  >>
end;

procedure ricci_aff(chr2_aff,i,j,vars);
% Ricci tensor of the affine connection with Christoffel symbols
% chr2_aff(i,j,k), R_{ij}
begin scalar n_gmat,tempricciaff;
  n_gmat:=length(vars);
  tempricciaff:={};
  return
  <<
    tempricciaff:=for s:=1:n_gmat collect riem2_aff(chr2_aff,s,i,s,j,vars);
    part(tempricciaff,0):=plus
  >>
end;

procedure scalar_curv(gmat,inv_gmat,chr2_name,vars);
% Scalar curvature of the Riemannian connection of gmat
begin scalar n_gmat,tempscurv;
  n_gmat:=length(vars);
  tempscurv:={};
   return
   <<
     tempscurv:=
       for i:=1:n_gmat join
         for j:=1:n_gmat collect
           inv_gmat(i,j)*ricci(gmat,chr2_name,i,j,vars);
     part(tempscurv,0):=plus
   >>
end;

procedure einstein(gmat,inv_gmat,chr2_name,i,j,vars);
% Einstein tensor of the Riemannian connection of gmat, R_{ij}
begin scalar inv_gmat;
   return
     ricci(gmat,chr2_name,i,j,vars)
       - (1/2)*scalar_curv(gmat,inv_gmat,chr2_name,vars)*gmat(i,j)
end;

procedure is_zero_riem2(gmat,chr2_name,vars);
% checks if the Riemannian curvature of the metric gmat is zero
begin scalar n_vars;
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      for m:=1:n_vars do
      if riem2(gmat,chr2_name,i,j,k,m,vars) neq 0
       then write "The Riemannian curvature is nonzero!";
end;

procedure is_zero_ricci(gmat,chr2_name,vars);
% checks if the Ricci tensor of the metric gmat is zero
begin scalar n_vars;
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     if ricci(gmat,chr2_name,i,j,vars) neq 0
      then write "The Ricci tensor is nonzero!";
end;

procedure is_zero_nabla_aff(chr2_aff,gmat,vars);
% checks if nabla(gmat) is zero
begin scalar n_vars;
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      if nabla_aff(chr2_aff,i,j,k,gmat,vars) neq 0
       then write "nabla(g) is nonzero!";
end;

procedure is_zero_riem2_aff(chr_aff,vars);
% checks if the Riemannian curvature of the metric gmat is zero
begin scalar n_vars;
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      for m:=1:n_vars do
      if riem2_aff(chr_aff,i,j,k,m,vars) neq 0
       then write "Curvature non-zero!";
end;

% Recall that if a pseudo-Riemannian manifold is Einstein,
% i.e. R_{ij}=kg_{ij}, k a constant, then R = kn (after metric contraction),
% so check first if R is constant, then divide by n to find k.

procedure is_constantcurv(gmat,chr2_name,vars);
begin scalar n_gmat,sectcurv,tempsc;
   n_gmat:=length(vars);
   sectcurv:=
   for a:=1:n_gmat join
    for b:=1:n_gmat join
     for c:=1:n_gmat join
      for d:=1:n_gmat join
       << tempsc:=gmat(a,c)*gmat(d,b) -
          gmat(a,d)*gmat(c,b);
          if tempsc neq 0 then
           {riem1(gmat,chr2_name,a,b,c,d,vars)/tempsc}
          else
          {}
       >>;
   for each el in sectcurv do
   <<
      if el neq first sectcurv then rederr
         "Metric with no constant sectional curvature"
   >>;
   return first sectcurv
end;

% riem3 produces the tensor R^{ij}_{kh}

procedure riem3(gmat,inv_gmat,chr2_name,i,j,k,l,vars);
begin scalar n_vars,tempriem3;
  n_vars:=length(vars);
  tempriem3:={};
  return
  <<
    tempriem3:=for s:=1:n_vars collect
      inv_gmat(i,s)*riem2(gmat,chr2_name,j,s,k,l,vars);
    part(tempriem3,0):=plus
  >>
end;

procedure is_zero_riem3(gmat,inv_gmat,chr2_name,vars);
% checks if the Riemannian curvature of the metric gmat is zero
begin scalar n_vars;
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      for m:=1:n_vars do
      if riem3(gmat,inv_gmat,chr2_name,i,j,k,m,vars) neq 0
       then write "The Riemannian curvature is nonzero!";
end;

% Sometimes we need Christoffel symbols with upper indexes; here we call them
% Christoffel symbols of type 3.

procedure chr3(gmat,inv_gmat,chr2_name,i,j,k,vars);
% Christoffel symbols of the second kind of gmat, \Gamma^{ij}_{k}
% inv_gmat should be an operator containing the inverse of gmat
% This procedure can be issued only after generate_all_chr2 has been run!
begin scalar n_gmat,tempchr3;
  n_gmat:=length(vars);
  tempchr3:={};
  return
  <<
    tempchr3:=for s:=1:n_gmat collect
      (- inv_gmat(i,s)*mk_chr2(chr2_name,j,s,k));
    part(tempchr3,0):=plus
  >>
end;

procedure mk_chr3(chr3_name,i,j,k);
% Generate a symbol from the table of all Christoffel symbols
   riemann_list2ids({chr3_name,i,j,k});

procedure generate_all_chr3(gmat,inv_gmat,chr2_name,chr3_name,vars);
% Generate all Christoffel symbols of type 3
begin scalar n_vars,list_done;
   list_done:={};
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      if not ({i,j,k} member list_done) then
      <<
       	set(mk_chr3(chr3_name,i,j,k),chr3(gmat,inv_gmat,chr2_name,i,j,k,vars));
	write i,j,k;
       list_done:={i,j,k} . list_done
      >>;
end;

% riem4 produces the tensor R^{ijk}_{h} using the formula from Dubrovin's paper
% flat pencils of riemannian metrics etc ...

procedure riem4(gmat,inv_gmat,chr3_name,i,j,k,l,vars);
% Contravariant curvature of the Riemannian connection of gmat, R^{ijk}_l
begin
  scalar n_gmat,tempriem4_1,tempriem4_2;
  n_gmat:=length(vars);
  tempriem4_1:=for s:=1:n_gmat collect
       inv_gmat(i,s)*(df(mk_chr3(chr3_name,j,k,l),part(vars,s)))
       	 - df(mk_chr3(chr3_name,j,k,s),part(vars,l));
  tempriem4_1:=part(tempriem4_1,0):=plus;
  tempriem4_2:=for s:=1:n_gmat collect
    mk_chr3(chr3_name,i,j,s)*mk_chr3(chr3_name,s,k,l)
      - mk_chr3(chr3_name,i,k,s)*mk_chr3(chr3_name,s,j,l);
  tempriem4_2:=part(tempriem4_2,0):=plus;
   return tempriem4_1 + tempriem4_2
end;

procedure is_zero_riem4(gmat,inv_gmat,chr3_name,vars);
% checks if the Riemannian curvature of the metric gmat is zero
begin scalar n_vars;
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      for m:=1:n_vars do
      if riem4(gmat,inv_gmat,chr3_name,i,j,k,m,vars) neq 0
       then write "The Riemannian curvature is nonzero!";
end;

% Sometimes we need Christoffel symbols with ALL upper indexes;
% here we call them Christoffel symbols of type 4.

procedure chr4(inv_gmat,i,j,k,vars);
% Christoffel symbols of the second kind of gmat, \Gamma^{kji}
% inv_gmat should be an operator containing the inverse of gmat
begin scalar n_gmat,tempchr4;
  n_gmat:=length(vars);
  tempchr4:={};
  return
  <<
    tempchr4:=for q:=1:n_gmat collect
      (1/2)*(
	df(inv_gmat(k,i),part(vars,q))*inv_gmat(q,j)
	  + df(inv_gmat(k,j),part(vars,q))*inv_gmat(q,i)
            - df(inv_gmat(j,i),part(vars,q))*inv_gmat(q,k)
	    );
    part(tempchr4,0):=plus
  >>
end;

procedure mk_chr4(chr4_name,i,j,k);
% Generate a symbol from the table of all Christoffel symbols
   riemann_list2ids({chr4_name,i,j,k});

procedure generate_all_chr4(inv_gmat,chr4_name,vars);
% Generate all Christoffel symbols of type 4
begin scalar n_vars,list_done;
   list_done:={};
   n_vars:=length(vars);
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      if not ({i,j,k} member list_done) then
      <<
       	set(mk_chr4(chr4_name,i,j,k),chr4(inv_gmat,i,j,k,vars));
	write i,j,k;
       list_done:={i,j,k} . list_done
      >>;
end;

procedure nijenhuis(ten,i,j,k,vars);
  % computes the Nijenhuis tensor 'nt(i,j,k)=nt^i_jk'
  % of the tensor 'ten(i,j)=ten^i_j',
  % which must be declared as an operator.
  begin scalar n_vars,tempterm;
    n_vars:=length(vars);
    return
      <<
        tempterm:=for alp:=1:n_vars collect
        df(ten(i,k),part(vars,alp))*ten(alp,j)
        - df(ten(i,j),part(vars,alp))*ten(alp,k)
      	+ (df(ten(alp,j),part(vars,k)) - df(ten(alp,k),part(vars,j)))
	  *ten(i,alp);
        tempterm:=part(tempterm,0):=plus
      >>
  end;

procedure mk_nt(ten,i,j,k,vars);
  riemann_list2ids({nt_,i,j,k});

procedure generate_all_nt(ten,vars);
  begin scalar n_vars,list_done;
   n_vars:=length(vars);
   list_done:={};
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      if not ({i,j,k} member list_done) then
      <<
       set(mk_nt(ten,i,j,k,vars),nijenhuis(ten,i,j,k,vars));
       list_done:={i,j,k} . list_done
      >>;
end;

procedure haantijes(ten,i,j,k,vars);
  % computes the Haantjies tensor 'ht(i,j,k)=ht^i_jk'
  % of the tensor 'ten(i,j)=ten^i_j',
  % which must be declared as an operator.
  begin scalar n_vars,tempterm;
    n_vars:=length(vars);
    return
      <<
        tempterm:=for alp:=1:n_vars join for bet:=1:n_vars collect
          ten(i,alp)*ten(alp,bet)*mk_nt(ten,bet,j,k,vars)
	    + mk_nt(ten,i,alp,bet,vars)*ten(alp,j)*ten(bet,k)
	  - ten(i,alp)*(
	    mk_nt(ten,alp,bet,k,vars)*ten(bet,j) +
	    mk_nt(ten,alp,j,bet,vars)*ten(bet,k)
		);
        tempterm:=part(tempterm,0):=plus
      >>
  end;

procedure mk_ht(ten,i,j,k,vars);
  riemann_list2ids({ht_,i,j,k});

procedure generate_all_ht(ten,vars);
  begin scalar n_vars,list_done;
   n_vars:=length(vars);
   list_done:={};
   for i:=1:n_vars do
    for j:=1:n_vars do
     for k:=1:n_vars do
      if not ({i,j,k} member list_done) then
      <<
       set(mk_ht(ten,i,j,k,vars),haantijes(ten,i,j,k,vars));
       list_done:={i,j,k} . list_done
      >>;
end;

;end;

Local Variables:
mode:reduce
End:
