
matrix hmet(3,3);


hmet(1,1):=(2*((u1*u3**2 - 4*u1*u3 + u2**3 + u2**2*u3 - 2*u2**2 + u2)**2 + (u1*
u3**2 - 4*u1*u3 - 2*u2**2*u3 + 4*u2**2 - 2*u2*u3**2 + 8*u2*u3 - 8*u2 - 2*u3 + 4)
*(u2**2 + 2*u2*u3 - 4*u2 + 3)*u1))/u1**8$


hmet(1,2):=(2*((2*(u2**2 + 5)*(u3 - 2)*u2 - (u3**2 - 4*u3 - 8) + 2*(u3**2 - 4*u3
 + 8)*u2**2)*u1 - ((u2**2 + 1 + (u3 - 2)*u2)*(u2**2 + 3)*u2 + (u3 - 2 + u2)*(u3 
- 4)*u1**2*u3)))/u1**7$


hmet(1,3):=( - 2*((u1*u2 + u1*u3 - 2*u1 + u2**2)*(u1*u3**2 - 4*u1*u3 + u2**3 + 
u2**2*u3 - 2*u2**2 + u2) - (u2**2 + 2*u2*u3 - 4*u2 + 3)**2*u1))/u1**7$


hmet(2,1):=(2*((2*(u2**2 + 5)*(u3 - 2)*u2 - (u3**2 - 4*u3 - 8) + 2*(u3**2 - 4*u3
 + 8)*u2**2)*u1 - ((u2**2 + 1 + (u3 - 2)*u2)*(u2**2 + 3)*u2 + (u3 - 2 + u2)*(u3 
- 4)*u1**2*u3)))/u1**7$


hmet(2,2):=( - 2*((2*((u2**2 + 1)*(u3 - 2) + 4*u2) - (u3 - 4)*u1*u3)*u1 - ((u2**
2 + 3)**2 + 8*(u3 - 2)*u2)))/u1**6$


hmet(2,3):=( - 2*(((2*u2**2 + 3)*(u3 - 2) + 10*u2)*u1 - ((u2 + 1)*(u2 - 1)*u2**2
 + (u3 - 4)*u1**2*u3)))/u1**6$


hmet(3,1):=( - 2*((u1*u2 + u1*u3 - 2*u1 + u2**2)*(u1*u3**2 - 4*u1*u3 + u2**3 + 
u2**2*u3 - 2*u2**2 + u2) - (u2**2 + 2*u2*u3 - 4*u2 + 3)**2*u1))/u1**7$


hmet(3,2):=( - 2*(((2*u2**2 + 3)*(u3 - 2) + 10*u2)*u1 - ((u2 + 1)*(u2 - 1)*u2**2
 + (u3 - 4)*u1**2*u3)))/u1**6$


hmet(3,3):=( - 2*((u2**2 + 3 + 2*(u3 - 2)*u2)*(u1 + 2*u2)*u1 - (u1*u2 + u1*u3 - 
2*u1 + u2**2)**2))/u1**6$


;end;
