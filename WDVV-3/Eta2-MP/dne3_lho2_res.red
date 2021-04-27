
matrix hmet(3,3);


hmet(1,1):=( - 2*((4*rho**4 - 8*rho**3*u2 + rho**3*u3**2 + 8*rho**2*u2**2 - 6*
rho**2*u2*u3**2 + rho**2*u3**4 + 4*rho*u1*u2*u3 - 2*rho*u1*u3**3 - 4*rho*u2**3 +
 3*rho*u2**2*u3**2 + u1**2*u3**2 - 2*u1*u2**2*u3 + u2**4)*(2*rho**2 - 2*rho*u2 +
 rho*u3**2 + u2**2) - (rho**2 - 4*rho*u2 + rho*u3**2 - u1*u3 + 2*u2**2)**2*rho*
u3**2))/((rho - u2)**8*rho**5)$


hmet(1,2):=( - 2*((4*rho**4 - 8*rho**3*u2 + rho**3*u3**2 + 8*rho**2*u2**2 - 6*
rho**2*u2*u3**2 + rho**2*u3**4 + 4*rho*u1*u2*u3 - 2*rho*u1*u3**3 - 4*rho*u2**3 +
 3*rho*u2**2*u3**2 + u1**2*u3**2 - 2*u1*u2**2*u3 + u2**4)*(rho*u3 + u1) - (2*rho
**2 - 2*rho*u2 + rho*u3**2 + u2**2)*(rho**2 - 4*rho*u2 + rho*u3**2 - u1*u3 + 2*
u2**2)*rho*u3))/((rho - u2)**7*rho**5)$


hmet(1,3):=(2*((2*rho**2 - 2*rho*u2 + rho*u3**2 + u2**2)**2 - (rho**2 - 4*rho*u2
 + rho*u3**2 - u1*u3 + 2*u2**2)*(rho*u3 + u1)*u3))/((rho - u2)**6*rho**4)$


hmet(2,1):=( - 2*((4*rho**4 - 8*rho**3*u2 + rho**3*u3**2 + 8*rho**2*u2**2 - 6*
rho**2*u2*u3**2 + rho**2*u3**4 + 4*rho*u1*u2*u3 - 2*rho*u1*u3**3 - 4*rho*u2**3 +
 3*rho*u2**2*u3**2 + u1**2*u3**2 - 2*u1*u2**2*u3 + u2**4)*(rho*u3 + u1) - (2*rho
**2 - 2*rho*u2 + rho*u3**2 + u2**2)*(rho**2 - 4*rho*u2 + rho*u3**2 - u1*u3 + 2*
u2**2)*rho*u3))/((rho - u2)**7*rho**5)$


hmet(2,2):=( - (2*(4*rho**4 - 8*rho**3*u2 + rho**3*u3**2 + 8*rho**2*u2**2 - 6*
rho**2*u2*u3**2 + rho**2*u3**4 + 4*rho*u1*u2*u3 - 2*rho*u1*u3**3 - 4*rho*u2**3 +
 3*rho*u2**2*u3**2 + u1**2*u3**2 - 2*u1*u2**2*u3 + u2**4)*(5*rho**3 - 2*rho**2*
u2 + rho*u2**2 + u1**2) - (2*rho**2 - 2*rho*u2 + rho*u3**2 + u2**2)**2*(rho - u2
)**2*rho - (2*rho**2 - 2*rho*u2 + rho*u3**2 + u2**2)**2*(rho - u2)**2*rho))/((
rho - u2)**8*rho**5)$


hmet(2,3):=( - 2*((5*rho**3 - 2*rho**2*u2 + rho*u2**2 + u1**2)*(rho**2 - 4*rho*
u2 + rho*u3**2 - u1*u3 + 2*u2**2)*u3 - (2*rho**2 - 2*rho*u2 + rho*u3**2 + u2**2)
*(rho*u3 + u1)*(rho - u2)**2))/((rho - u2)**7*rho**4)$


hmet(3,1):=(2*((2*rho**2 - 2*rho*u2 + rho*u3**2 + u2**2)**2 - (rho**2 - 4*rho*u2
 + rho*u3**2 - u1*u3 + 2*u2**2)*(rho*u3 + u1)*u3))/((rho - u2)**6*rho**4)$


hmet(3,2):=( - 2*((5*rho**3 - 2*rho**2*u2 + rho*u2**2 + u1**2)*(rho**2 - 4*rho*
u2 + rho*u3**2 - u1*u3 + 2*u2**2)*u3 - (2*rho**2 - 2*rho*u2 + rho*u3**2 + u2**2)
*(rho*u3 + u1)*(rho - u2)**2))/((rho - u2)**7*rho**4)$


hmet(3,3):=( - 2*(10*rho**4 - 14*rho**3*u2 + 4*rho**3*u3**2 - 2*rho**2*u1*u3 + 
11*rho**2*u2**2 + rho*u1**2 + 4*rho*u1*u2*u3 - 4*rho*u2**3 + u1**2*u3**2 - 2*u1*
u2**2*u3 + u2**4))/((rho - u2)**6*rho**3)$


;end;

