
crack_results:={{{},
{f=((rho - u2)**8*c_3)/((u1*u3 - u2**2)**2*u1**2 + 32*rho**7 - (96*u2 - 13*u3**2
)*rho**6 + 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**2*u3 - 2*u2**4)*(u1*u3 - u2**2
)*rho + 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)*rho**5 + 2*(2*(18*u2 - u3**2)
*u2**3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2)*u1*u2*u3)*rho**3 - (((24*u2 
- u3**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - (8*u2**2 - 16*u2*u3**2 + u3**4
)*u1**2)*rho**2 - 2*((64*u2 - 13*u3**2)*u2**2 - 2*u1**2 - (22*u2 - 5*u3**2)*u1*
u3)*rho**4)},
{c_3},
{c_3}}};


c_3:=1/2;


matrix gl1(3,3);


matrix gu1(3,3);


gl1(1,1):=(2*((u1*u3 - u2**2)**2*u2**2 + 8*rho**6 - (24*u2 - 5*u3**2)*rho**5 + (
36*u2**2 - 14*u2*u3**2 + u3**4)*rho**4 + 2*(u1*u3 - 3*u2**2)**2*rho**2 - 2*(u1*
u3 - u2**2)*(u1*u3 - 3*u2**2)*rho*u2 - ((32*u2 - 7*u3**2)*u2**2 - 2*(4*u2 - u3**
2)*u1*u3)*rho**3)*c_3)/(((96*u2 - 13*u3**2 - 32*rho)*rho**6 - (u1*u3 - u2**2)**2
*u1**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**2*u3 - 2*u2**4)*(u1*u3 - u2**2)*
rho - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)*rho**5 - 2*(2*(18*u2 - u3**2)*
u2**3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2)*u1*u2*u3)*rho**3 + (((24*u2 -
 u3**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - (8*u2**2 - 16*u2*u3**2 + u3**4)
*u1**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*u1**2 - (22*u2 - 5*u3**2)*u1*u3
)*rho**4)*rho**5)$


gl1(1,2):=(2*(2*rho**5*u3 + 4*rho**4*u1 + 2*rho**4*u2*u3 - 2*rho**4*u3**3 - 8*
rho**3*u1*u2 + 3*rho**3*u1*u3**2 - 5*rho**3*u2**2*u3 + 8*rho**2*u1*u2**2 - 4*rho
**2*u1*u2*u3**2 + 4*rho**2*u2**3*u3 + 4*rho*u1**2*u2*u3 - rho*u1**2*u3**3 - 4*
rho*u1*u2**3 + 2*rho*u1*u2**2*u3**2 - rho*u2**4*u3 + u1**3*u3**2 - 2*u1**2*u2**2
*u3 + u1*u2**4)*(rho - u2)*c_3)/(((96*u2 - 13*u3**2 - 32*rho)*rho**6 - (u1*u3 - 
u2**2)**2*u1**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**2*u3 - 2*u2**4)*(u1*u3 
- u2**2)*rho - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)*rho**5 - 2*(2*(18*u2 -
 u3**2)*u2**3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2)*u1*u2*u3)*rho**3 + ((
(24*u2 - u3**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - (8*u2**2 - 16*u2*u3**2 
+ u3**4)*u1**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*u1**2 - (22*u2 - 5*u3**
2)*u1*u3)*rho**4)*rho**5)$


gl1(1,3):=( - 2*(4*rho**4 - 8*rho**3*u2 + 3*rho**3*u3**2 - rho**2*u1*u3 + 8*rho
**2*u2**2 + 4*rho*u1*u2*u3 - 4*rho*u2**3 + u1**2*u3**2 - 2*u1*u2**2*u3 + u2**4)*
(rho - u2)**2*c_3)/(((96*u2 - 13*u3**2 - 32*rho)*rho**6 - (u1*u3 - u2**2)**2*u1
**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**2*u3 - 2*u2**4)*(u1*u3 - u2**2)*rho
 - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)*rho**5 - 2*(2*(18*u2 - u3**2)*u2**
3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2)*u1*u2*u3)*rho**3 + (((24*u2 - u3
**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - (8*u2**2 - 16*u2*u3**2 + u3**4)*u1
**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*u1**2 - (22*u2 - 5*u3**2)*u1*u3)*
rho**4)*rho**4)$


gl1(2,1):=(2*(2*rho**5*u3 + 4*rho**4*u1 + 2*rho**4*u2*u3 - 2*rho**4*u3**3 - 8*
rho**3*u1*u2 + 3*rho**3*u1*u3**2 - 5*rho**3*u2**2*u3 + 8*rho**2*u1*u2**2 - 4*rho
**2*u1*u2*u3**2 + 4*rho**2*u2**3*u3 + 4*rho*u1**2*u2*u3 - rho*u1**2*u3**3 - 4*
rho*u1*u2**3 + 2*rho*u1*u2**2*u3**2 - rho*u2**4*u3 + u1**3*u3**2 - 2*u1**2*u2**2
*u3 + u1*u2**4)*(rho - u2)*c_3)/(((96*u2 - 13*u3**2 - 32*rho)*rho**6 - (u1*u3 - 
u2**2)**2*u1**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**2*u3 - 2*u2**4)*(u1*u3 
- u2**2)*rho - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)*rho**5 - 2*(2*(18*u2 -
 u3**2)*u2**3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2)*u1*u2*u3)*rho**3 + ((
(24*u2 - u3**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - (8*u2**2 - 16*u2*u3**2 
+ u3**4)*u1**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*u1**2 - (22*u2 - 5*u3**
2)*u1*u3)*rho**4)*rho**5)$


gl1(2,2):=(2*((u1*u3 - u2**2)**2*u1**2 + 16*rho**7 - (32*u2 - u3**2)*rho**6 + 4*
(8*u2**2 - 5*u2*u3**2 + u3**4)*rho**5 + 2*(2*u1*u2 - u1*u3**2 + u2**2*u3)*(u1*u3
 - u2**2)*rho*u1 - 2*((4*u2 - 3*u3**2)*u1**2 - 2*(u2 - u3**2)*u2**3 + (9*u2 - 2*
u3**2)*u1*u2*u3)*rho**3 + ((2*(4*u2 - u3**2)*u1 + u2**2*u3)*u2**2*u3 + (8*u2**2 
- 8*u2*u3**2 + u3**4)*u1**2)*rho**2 - 2*((8*u2 - 7*u3**2)*u2**2 - 2*u1**2 - 5*(2
*u2 - u3**2)*u1*u3)*rho**4)*c_3)/(((96*u2 - 13*u3**2 - 32*rho)*rho**6 - (u1*u3 -
 u2**2)**2*u1**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**2*u3 - 2*u2**4)*(u1*u3
 - u2**2)*rho - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)*rho**5 - 2*(2*(18*u2 
- u3**2)*u2**3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2)*u1*u2*u3)*rho**3 + (
((24*u2 - u3**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - (8*u2**2 - 16*u2*u3**2
 + u3**4)*u1**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*u1**2 - (22*u2 - 5*u3
**2)*u1*u3)*rho**4)*rho**5)$


gl1(2,3):=(2*(3*rho**5*u3 - 2*rho**4*u1 - 16*rho**4*u2*u3 + 4*rho**4*u3**3 + 6*
rho**3*u1*u2 - 6*rho**3*u1*u3**2 + 12*rho**3*u2**2*u3 + rho**2*u1**2*u3 - 7*rho
**2*u1*u2**2 + 4*rho**2*u1*u2*u3**2 - 4*rho**2*u2**3*u3 - 4*rho*u1**2*u2*u3 + 
rho*u1**2*u3**3 + 4*rho*u1*u2**3 - 2*rho*u1*u2**2*u3**2 + rho*u2**4*u3 - u1**3*
u3**2 + 2*u1**2*u2**2*u3 - u1*u2**4)*(rho - u2)*c_3)/(((96*u2 - 13*u3**2 - 32*
rho)*rho**6 - (u1*u3 - u2**2)**2*u1**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**
2*u3 - 2*u2**4)*(u1*u3 - u2**2)*rho - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)
*rho**5 - 2*(2*(18*u2 - u3**2)*u2**3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2
)*u1*u2*u3)*rho**3 + (((24*u2 - u3**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - 
(8*u2**2 - 16*u2*u3**2 + u3**4)*u1**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*
u1**2 - (22*u2 - 5*u3**2)*u1*u3)*rho**4)*rho**4)$


gl1(3,1):=( - 2*(4*rho**4 - 8*rho**3*u2 + 3*rho**3*u3**2 - rho**2*u1*u3 + 8*rho
**2*u2**2 + 4*rho*u1*u2*u3 - 4*rho*u2**3 + u1**2*u3**2 - 2*u1*u2**2*u3 + u2**4)*
(rho - u2)**2*c_3)/(((96*u2 - 13*u3**2 - 32*rho)*rho**6 - (u1*u3 - u2**2)**2*u1
**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**2*u3 - 2*u2**4)*(u1*u3 - u2**2)*rho
 - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)*rho**5 - 2*(2*(18*u2 - u3**2)*u2**
3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2)*u1*u2*u3)*rho**3 + (((24*u2 - u3
**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - (8*u2**2 - 16*u2*u3**2 + u3**4)*u1
**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*u1**2 - (22*u2 - 5*u3**2)*u1*u3)*
rho**4)*rho**4)$


gl1(3,2):=(2*(3*rho**5*u3 - 2*rho**4*u1 - 16*rho**4*u2*u3 + 4*rho**4*u3**3 + 6*
rho**3*u1*u2 - 6*rho**3*u1*u3**2 + 12*rho**3*u2**2*u3 + rho**2*u1**2*u3 - 7*rho
**2*u1*u2**2 + 4*rho**2*u1*u2*u3**2 - 4*rho**2*u2**3*u3 - 4*rho*u1**2*u2*u3 + 
rho*u1**2*u3**3 + 4*rho*u1*u2**3 - 2*rho*u1*u2**2*u3**2 + rho*u2**4*u3 - u1**3*
u3**2 + 2*u1**2*u2**2*u3 - u1*u2**4)*(rho - u2)*c_3)/(((96*u2 - 13*u3**2 - 32*
rho)*rho**6 - (u1*u3 - u2**2)**2*u1**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**
2*u3 - 2*u2**4)*(u1*u3 - u2**2)*rho - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)
*rho**5 - 2*(2*(18*u2 - u3**2)*u2**3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2
)*u1*u2*u3)*rho**3 + (((24*u2 - u3**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - 
(8*u2**2 - 16*u2*u3**2 + u3**4)*u1**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*
u1**2 - (22*u2 - 5*u3**2)*u1*u3)*rho**4)*rho**4)$


gl1(3,3):=(2*(10*rho**4 - 14*rho**3*u2 + 4*rho**3*u3**2 - 2*rho**2*u1*u3 + 11*
rho**2*u2**2 + rho*u1**2 + 4*rho*u1*u2*u3 - 4*rho*u2**3 + u1**2*u3**2 - 2*u1*u2
**2*u3 + u2**4)*(rho - u2)**2*c_3)/(((96*u2 - 13*u3**2 - 32*rho)*rho**6 - (u1*u3
 - u2**2)**2*u1**2 - 2*(2*u1**2*u2 - u1**2*u3**2 + 3*u1*u2**2*u3 - 2*u2**4)*(u1*
u3 - u2**2)*rho - 4*(36*u2**2 - 11*u2*u3**2 + u3**4 - u1*u3)*rho**5 - 2*(2*(18*
u2 - u3**2)*u2**3 - (4*u2 - 5*u3**2)*u1**2 - (31*u2 - 2*u3**2)*u1*u2*u3)*rho**3 
+ (((24*u2 - u3**2)*u2**2 - 2*(20*u2 - u3**2)*u1*u3)*u2**2 - (8*u2**2 - 16*u2*u3
**2 + u3**4)*u1**2)*rho**2 + 2*((64*u2 - 13*u3**2)*u2**2 - 2*u1**2 - (22*u2 - 5*
u3**2)*u1*u3)*rho**4)*rho**3)$


gu1(1,1):=( - (5*rho**3 - 2*rho**2*u2 + rho*u2**2 + u1**2)*rho**3)/(2*c_3)$


gu1(1,2):=((rho*u3 + u1)*(rho - u2)*rho**3)/(2*c_3)$


gu1(1,3):=( - (2*rho**2 + u2**2 - (2*u2 - u3**2)*rho)*rho**3)/(2*c_3)$


gu1(2,1):=((rho*u3 + u1)*(rho - u2)*rho**3)/(2*c_3)$


gu1(2,2):=( - (2*rho**2 + u2**2 - (2*u2 - u3**2)*rho)*rho**3)/(2*c_3)$


gu1(2,3):=((rho**2 - 4*rho*u2 + rho*u3**2 - u1*u3 + 2*u2**2)*rho**3*u3)/(2*(rho 
- u2)*c_3)$


gu1(3,1):=( - (2*rho**2 + u2**2 - (2*u2 - u3**2)*rho)*rho**3)/(2*c_3)$


gu1(3,2):=((rho**2 - 4*rho*u2 + rho*u3**2 - u1*u3 + 2*u2**2)*rho**3*u3)/(2*(rho 
- u2)*c_3)$


gu1(3,3):=( - (4*rho**4 - 8*rho**3*u2 + rho**3*u3**2 + 8*rho**2*u2**2 - 6*rho**2
*u2*u3**2 + rho**2*u3**4 + 4*rho*u1*u2*u3 - 2*rho*u1*u3**3 - 4*rho*u2**3 + 3*rho
*u2**2*u3**2 + u1**2*u3**2 - 2*u1*u2**2*u3 + u2**4)*rho**2)/(2*(rho - u2)**2*c_3
)$


;end;
