# JACOBI
#
# A package for the computation of the Jacobi property for Poisson brackets
#

#
# See https://gdeq.org/Weakly_nonlocal_Poisson_brackets for further details
#
# Authors: M. Casati, P. Lorenzoni, D. Valeri, R. Vitolo (2021)
#
#  L i c e n s e
#
# JACOBI is a free software distributed under the terms of the GNU General 
# Public License <http://www.gnu.org/copyleft/gpl.html> as published by 
# the Free Software Foundation.
#
# In particular, JACOBI comes with ABSOLUTELY NO WARRANTY.
#
# Version history
#
# Version 1.0, 15 January 2021

print(`JACOBI 1.0 for Maple 2020`);
print(`Authors: M. Casati, P. Lorenzoni, D. Valeri, R. Vitolo`);
print(`Web site: https://gdeq.org/Weakly_nonlocal_Poisson_brackets`);

Schouten_bracket:= proc(P,Q,T,N,M)
  description "Calculate the Schouten bracket [P,Q]",
              "N: number of components of the operators P,Q;",
              "M: order of derivatives in P,Q",
	      "T: the three-vector T=[P,Q]";

  local P_xy,P_yx,P_xz,P_zx,P_zy,P_yz,Q_xy,Q_yx,Q_xz,Q_zx,Q_yz,Q_zy,
  i,j,k,l,r,s,t,T0,T1,T2,cfnl_xyxz,cfnl_zxzy,cfnl_yzyx,cfl_xyxz:
  global delta:

  print("Step 0: calculating Dubrovin-Zhang formula");

# Calculate the total derivatives of the operator P
  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to M do
        P[i,j,k]:=add(
	  add(
	    diff(P[i,j,k-1],u[q,x,s])*u[q,x,s+1],
	    s=0..M-1),
	  q=1..N)
	  + add(
	      diff(P[i,j,k-1],delta[x-y,s])*delta[x-y,s+1],
	    s=-1..M-1)
      end do
    end do
  end do:

#Generate the operators P in all variables needed in Dubrovin-Zhang formula
  P_xy:=P:
  P_yx:=subs({x=y,y=x},P_xy):
  P_xz:=subs(y=z,P_xy):
  P_zx:=subs(y=z,P_yx):
  P_yz:=subs(x=y,P_xz):
  P_zy:=subs(x=z,P_xy):

# Calculate the total derivatives of the operator Q
  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to M do
        Q[i,j,k]:=add(
	  add(
	    diff(Q[i,j,k-1],u[q,x,s])*u[q,x,s+1],
	    s=0..M-1),
	  q=1..N)
	  + add(
	      diff(Q[i,j,k-1],delta[x-y,s])*delta[x-y,s+1],
	    s=-1..M-1)
      end do
    end do
  end do:

#Generate the operators Q in all variables needed in Dubrovin-Zhang formula
  Q_xy:=Q:
  Q_yx:=subs({x=y,y=x},Q_xy):
  Q_xz:=subs(y=z,Q_xy):
  Q_zx:=subs(y=z,Q_yx):
  Q_yz:=subs(x=y,Q_xz):
  Q_zy:=subs(x=z,Q_xy):

# The three-vector T0 from Dubrovin-Zhang formula
T0:=Array(1..N,1..N,1..N):

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        T0[i,j,k]:=
	add(add(diff(P_xy[i,j,0],u[l,x,s])*Q_xz[l,k,s],s=0..M)
	+ subs(delta[x-y,-1]=-delta[y-x,-1],
	    add(diff(P_xy[i,j,0],u[l,y,s])*Q_yz[l,k,s],s=0..M))
	+ add(diff(P_zx[k,i,0],u[l,z,s])*Q_zy[l,j,s],s=0..M)
	+ subs(delta[z-x,-1]=-delta[x-z,-1],
	    add(diff(P_zx[k,i,0],u[l,x,s])*Q_xy[l,j,s],s=0..M))
	+ add(diff(P_yz[j,k,0],u[l,y,s])*Q_yx[l,i,s],s=0..M)
	+ subs(delta[y-z,-1]=-delta[z-y,-1],
	    add(diff(P_yz[j,k,0],u[l,z,s])*Q_zx[l,i,s],s=0..M))
	+ add(diff(Q_xy[i,j,0],u[l,x,s])*P_xz[l,k,s],s=0..M)
	+ subs(delta[x-y,-1]=-delta[y-x,-1],
	    add(diff(Q_xy[i,j,0],u[l,y,s])*P_yz[l,k,s],s=0..M))
	+ add(diff(Q_zx[k,i,0],u[l,z,s])*P_zy[l,j,s],s=0..M)
	+ subs(delta[z-x,-1]=-delta[x-z,-1],
	    add(diff(Q_zx[k,i,0],u[l,x,s])*P_xy[l,j,s],s=0..M))
	+ add(diff(Q_yz[j,k,0],u[l,y,s])*P_yx[l,i,s],s=0..M)
	+ subs(delta[y-z,-1]=-delta[z-y,-1],
	    add(diff(Q_yz[j,k,0],u[l,z,s])*P_zx[l,i,s],s=0..M))
	    ,l=1..N)
      end do
    end do
  end do:

# Here we calculate the step 1 of the algorithm
# enhanced by a first application of the step 3
# in order to reconstruct a new three-vector T1
# which is equivalent to T0 up to total derivatives.

print("Step 1 of the algorithm");

# Replacing nu(z-y)*delta(z-x)
  delta[z-y,-1,z-x,0]:=delta[x-y,-1]*delta[x-z,0]:
  for i from 1 to M-1 do
    delta[z-y,-1,z-x,i]:= - add(diff(delta[z-y,-1,z-x,i-1],
      delta[x-y,k])*delta[x-y,k+1],k=-1..M)
       - add(diff(delta[z-y,-1,z-x,i-1],
         delta[x-z,k])*delta[x-z,k+1],k=-1..M)
  end do:

# Replacing nu(y-x)*delta(y-z)
  delta[y-x,-1,y-z,0]:=delta[z-x,-1]*delta[z-y,0]:
  for i from 1 to M-1 do
    delta[y-x,-1,y-z,i]:= - add(diff(delta[y-x,-1,y-z,i-1],
      delta[z-x,k])*delta[z-x,k+1],k=-1..M)
       - add(diff(delta[y-x,-1,y-z,i-1],
         delta[z-y,k])*delta[z-y,k+1],k=-1..M)
  end do:

# Replacing nu(x-z)*delta(x-y)
  delta[x-z,-1,x-y,0]:=delta[y-z,-1]*delta[y-x,0]:
  for i from 1 to M-1 do
  delta[x-z,-1,x-y,i]:= - add(diff(delta[x-z,-1,x-y,i-1],
    delta[y-z,k])*delta[y-z,k+1],k=-1..M)
     - add(diff(delta[x-z,-1,x-y,i-1],
       delta[y-x,k])*delta[y-x,k+1],k=-1..M)
  end do:

# Replacing all products of delta's to products of the form
# delta^(m)(x-y)*delta^(n)(x-z)
  for l from 0 to M do
    delta[x-y,0,y-z,l]:=delta[x-y,0]*delta[x-z,l]
  end do:

  for k from 1 to M do
    for l from 0 to M do
      delta[x-y,k,y-z,l]:=add(diff(delta[x-y,k-1,y-z,l],delta[x-y,m])
        *delta[x-y,m+1],m=-1..M)
        +add(diff(delta[x-y,k-1,y-z,l],delta[x-z,m])*delta[x-z,m+1],m=-1..M)
    end do
  end do:

  for l from 0 to M do
    delta[z-x,0,z-y,l]:=delta[x-y,l]*delta[x-z,0]
  end do:

  for k from 1 to M do
    for l from 0 to M do
      delta[z-x,k,z-y,l]:=-add(diff(delta[z-x,k-1,z-y,l],delta[x-y,m])
        *delta[x-y,m+1],m=-1..M)
	 - add(diff(delta[z-x,k-1,z-y,l],delta[x-z,m])
        *delta[x-z,m+1],m=-1..M)
    end do
  end do:

  for k from 0 to M do
    for l from 0 to M do
      delta[z-x,k,x-y,l]:=(-1)^k*delta[x-y,l]*delta[x-z,k]
    end do
  end do:

  for k from 0 to M do
    delta[y-z,k,y-x,0]:=delta[x-y,0]*delta[x-z,k]
  end do:

  for l from 1 to M do
    for k from 0 to M do
      delta[y-z,k,y-x,l]:=-add(diff(delta[y-z,k,y-x,l-1],delta[x-y,m])
        *delta[x-y,m+1],m=-1..M)
	-add(diff(delta[y-z,k,y-x,l-1],delta[x-z,m])
	*delta[x-z,m+1],m=-1..M)
    end do
  end do:

  for k from 0 to M do
    delta[y-z,k,z-x,0]:=(-1)^k*delta[x-y,k]*delta[x-z,0]
  end do:

  for l from 1 to M do
    for k from 0 to M do
      delta[y-z,k,z-x,l]:=-add(diff(delta[y-z,k,z-x,l-1],delta[x-y,m])
        *delta[x-y,m+1],m=-1..M)
	-add(diff(delta[y-z,k,z-x,l-1],delta[x-z,m])
	*delta[x-z,m+1],m=-1..M)
    end do
  end do:

# The three-vector T1
T1:=Array(1..N,1..N,1..N):

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        T1[i,j,k]:=
	  coeff(coeff(T0[i,j,k],delta[x-y,-1]),delta[x-z,-1])
	  *delta[x-y,-1]*delta[x-z,-1]
	  + coeff(coeff(T0[i,j,k],delta[y-x,-1]),delta[y-z,-1])
	  *delta[y-x,-1]*delta[y-z,-1]
	  + coeff(coeff(T0[i,j,k],delta[z-x,-1]),delta[z-y,-1])
	  *delta[z-x,-1]*delta[z-y,-1]
	  + add(coeff(coeff(T0[i,j,k],delta[z-y,-1]),delta[z-x,m])
	  *delta[z-y,-1,z-x,m],m=0..M)
	  + add(coeff(coeff(T0[i,j,k],delta[x-y,-1]),delta[x-z,m])
	  *delta[x-y,-1]*delta[x-z,m],m=0..M)
	  + add(coeff(coeff(T0[i,j,k],delta[y-x,-1]),delta[y-z,m])
	  *delta[y-x,-1,y-z,m],m=0..M)
	  + add(coeff(coeff(T0[i,j,k],delta[z-x,-1]),delta[z-y,m])
	  *delta[z-x,-1]*delta[z-y,m],m=0..M)
	  + add(coeff(coeff(T0[i,j,k],delta[x-z,-1]),delta[x-y,m])
	  *delta[x-z,-1,x-y,m],m=0..M)
	  + add(coeff(coeff(T0[i,j,k],delta[y-z,-1]),delta[y-x,m])
	  *delta[y-z,-1]*delta[y-x,m],m=0..M)
	  + add(add(coeff(coeff(T0[i,j,k],delta[x-y,l]),delta[x-z,m])
	  *delta[x-y,l]*delta[x-z,m],l=0..M),m=0..M)
	  + add(add(coeff(coeff(T0[i,j,k],delta[x-y,l]),delta[y-z,m])
	  *delta[x-y,l,y-z,m],l=0..M),m=0..M)
	  + add(add(coeff(coeff(T0[i,j,k],delta[z-x,l]),delta[z-y,m])
	  *delta[z-x,l,z-y,m],l=0..M),m=0..M)
	  + add(add(coeff(coeff(T0[i,j,k],delta[z-x,l]),delta[x-y,m])
	  *delta[z-x,l,x-y,m],l=0..M),m=0..M)
	  + add(add(coeff(coeff(T0[i,j,k],delta[y-z,l]),delta[y-x,m])
	  *delta[y-z,l,y-x,m],l=0..M),m=0..M)
	  + add(add(coeff(coeff(T0[i,j,k],delta[y-z,l]),delta[z-x,m])
	  *delta[y-z,l,z-x,m],l=0..M),m=0..M)
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        T1[i,j,k]:=coeff(coeff(T1[i,j,k],delta[x-y,-1]),delta[x-z,-1])
	*delta[x-y,-1]*delta[x-z,-1]
	+ coeff(coeff(T1[i,j,k],delta[y-x,-1]),delta[y-z,-1])
	*delta[y-x,-1]*delta[y-z,-1]
	+ coeff(coeff(T1[i,j,k],delta[z-x,-1]),delta[z-y,-1])
	*delta[z-x,-1]*delta[z-y,-1]
	+ add(coeff(coeff(T1[i,j,k],delta[z-y,-1]),delta[z-x,m])
	*delta[z-y,-1,z-x,m],m=0..M)
	+ add(coeff(coeff(T1[i,j,k],delta[x-y,-1]),delta[x-z,m])
	*delta[x-y,-1]*delta[x-z,m],m=0..M)
	+ add(coeff(coeff(T1[i,j,k],delta[y-x,-1]),delta[y-z,m])
	*delta[y-x,-1,y-z,m],m=0..M)
	+ add(coeff(coeff(T1[i,j,k],delta[z-x,-1]),delta[z-y,m])
	*delta[z-x,-1]*delta[z-y,m],m=0..M)
	+ add(coeff(coeff(T1[i,j,k],delta[x-z,-1]),delta[x-y,m])
	*delta[x-z,-1,x-y,m],m=0..M)
	+ add(coeff(coeff(T1[i,j,k],delta[y-z,-1]),delta[y-x,m])
	*delta[y-z,-1]*delta[y-x,m],m=0..M)
	+ add(add(coeff(coeff(T1[i,j,k],delta[x-y,l]),delta[x-z,m])
	*delta[x-y,l]*delta[x-z,m],l=0..M),m=0..M)
	+ add(add(coeff(coeff(T1[i,j,k],delta[x-y,l]),delta[y-z,m])
	*delta[x-y,l,y-z,m],l=0..M),m=0..M)
	+ add(add(coeff(coeff(T1[i,j,k],delta[z-x,l]),delta[z-y,m])
	*delta[z-x,l,z-y,m],l=0..M),m=0..M)
	+ add(add(coeff(coeff(T1[i,j,k],delta[z-x,l]),delta[x-y,m])
	*delta[z-x,l,x-y,m],l=0..M),m=0..M)
	+ add(add(coeff(coeff(T1[i,j,k],delta[y-z,l]),delta[y-x,m])
	*delta[y-z,l,y-x,m],l=0..M),m=0..M)
	+ add(add(coeff(coeff(T1[i,j,k],delta[y-z,l]),delta[z-x,m])
	*delta[y-z,l,z-x,m],l=0..M),m=0..M)
      end do
    end do
  end do:

# Here we calculate the step 2 of the algorithm

print("Step 2 of the algorithm");

# The three-vector T2
T2:=Array(1..N,1..N,1..N):

# Array for coefficients
cfnl_xyxz:=Array(1..N,1..N,1..N,0..M,0..M):
cfnl_zxzy:=Array(1..N,1..N,1..N,0..M,0..M):
cfnl_yzyx:=Array(1..N,1..N,1..N,0..M,0..M):
cfl_xyxz:=Array(1..N,1..N,1..N,0..M,0..M,0..M):

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  cfnl_xyxz[i,j,k,r,0]:=
	  coeff(coeff(T1[i,j,k],delta[x-y,-1]),delta[x-z,r])
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  for s from 1 to M do
	    cfnl_xyxz[i,j,k,r,s]:=
	    add(add(diff(cfnl_xyxz[i,j,k,r,s-1],u[l,z,t])
	    *u[l,z,t+1],t=0..M),l=1..N)
	  end do
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  cfnl_zxzy[i,j,k,r,0]:=
	  coeff(coeff(T1[i,j,k],delta[z-x,-1]),delta[z-y,r])
        end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  for s from 1 to M do
	    cfnl_zxzy[i,j,k,r,s]:=
	    add(add(diff(cfnl_zxzy[i,j,k,r,s-1],u[l,y,t])
	    *u[l,y,t+1],t=0..M),l=1..N)
	  end do
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  cfnl_yzyx[i,j,k,r,0]:=
	  coeff(coeff(T1[i,j,k],delta[y-z,-1]),delta[y-x,r])
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  for s from 1 to M do
	    cfnl_yzyx[i,j,k,r,s]:=add(add(diff(cfnl_yzyx[i,j,k,r,s-1],u[l,x,t])
	    *u[l,x,t+1],t=0..M),l=1..N)
	  end do
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  for s from 0 to M do
	    cfl_xyxz[i,j,k,r,s,0]:=
	    coeff(coeff(T1[i,j,k],delta[x-y,r]),delta[x-z,s])
	  end do
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  for s from 0 to M do
	    for t from 1 to M do
	      cfl_xyxz[i,j,k,r,s,t]:=
	      add(add(diff(cfl_xyxz[i,j,k,r,s,t-1],u[l,y,p])
	      *u[l,y,p+1],p=0..M),l=1..N)
	    end do
	  end do
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        T2[i,j,k]:=coeff(coeff(T1[i,j,k],delta[x-y,-1]),delta[x-z,-1])
	*delta[x-y,-1]*delta[x-z,-1]
	+ coeff(coeff(T1[i,j,k],delta[y-x,-1]),delta[y-z,-1])
	*delta[y-x,-1]*delta[y-z,-1]
	+ coeff(coeff(T1[i,j,k],delta[z-x,-1]),delta[z-y,-1])
	*delta[z-x,-1]*delta[z-y,-1]
	+ delta[x-y,-1]*add(add(binomial(m,s)*subs(z=x,cfnl_xyxz[i,j,k,m,s])
	*delta[x-z,m-s],s=0..m),m=0..M)
	+ delta[z-x,-1]*add(add(binomial(m,s)*subs(y=z,cfnl_zxzy[i,j,k,m,s])
	*delta[z-y,m-s],s=0..m),m=0..M)
	+ delta[y-z,-1]*add(add(binomial(m,s)*subs(x=y,cfnl_yzyx[i,j,k,m,s])
	*delta[y-x,m-s],s=0..m),m=0..M)
	+ add(add(add(binomial(l,s)*subs(y=x,cfl_xyxz[i,j,k,l,m,s])
	*delta[x-y,l-s],s=0..l)*delta[x-z,m],l=0..M),m=0..M)
      end do
    end do
  end do:

# Here we calculate the step 3 of the algorithm

# The three-vector T is set equal to the result
# of the third step of the algorithm

print("Step 3 of the algorithm");

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  for s from 0 to M do
	    cfl_xyxz[i,j,k,r,s,0]:=coeff(coeff(T2[i,j,k],delta[x-y,r]),
	    delta[x-z,s])
	  end do
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        for r from 0 to M do
	  for s from 0 to M do
	    for t from 1 to M do
	      cfl_xyxz[i,j,k,r,s,t]:=
	      add(add(diff(cfl_xyxz[i,j,k,r,s,t-1],u[l,z,p])
	      *u[l,z,p+1],p=0..M),l=1..N)
	    end do
	  end do
	end do
      end do
    end do
  end do:

  for i from 1 to N do
    for j from 1 to N do
      for k from 1 to N do
        T[i,j,k]:=simplify(coeff(coeff(T2[i,j,k],delta[x-y,-1]),delta[x-z,-1])
	*delta[x-y,-1]*delta[x-z,-1]
	+ coeff(coeff(T2[i,j,k],delta[y-x,-1]),delta[y-z,-1])
	*delta[y-x,-1]*delta[y-z,-1]
	+ coeff(coeff(T2[i,j,k],delta[z-x,-1]),delta[z-y,-1])
	*delta[z-x,-1]*delta[z-y,-1]
	+ add(coeff(coeff(T2[i,j,k],delta[x-y,-1]),delta[x-z,m])
	*delta[x-y,-1]*delta[x-z,m],m=0..M)
	+ add(coeff(coeff(T2[i,j,k],delta[z-x,-1]),delta[z-y,m])
	*delta[z-x,-1]*delta[z-y,m],m=0..M)
	+ add(coeff(coeff(T2[i,j,k],delta[y-z,-1]),delta[y-x,m])
	*delta[y-z,-1]*delta[y-x,m],m=0..M)
	+ add(add(add(binomial(m,s)*subs(z=x,cfl_xyxz[i,j,k,l,m,s])
	*delta[x-z,m-s],s=0..m)*delta[x-y,l],m=0..M),l=0..M))
      end do
    end do
  end do:

end proc:
