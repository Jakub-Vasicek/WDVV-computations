
matrix gl3(3,3);


gl3(1,1):=(mu*rho**2 + u2**2)*cf(1);


gl3(1,2):=( - (mu*u1 - rho*u3)*cf(1)*u2)/mu;


gl3(1,3):=( - cf(1)*rho*u2**2)/mu;


gl3(2,1):=( - (mu*u1 - rho*u3)*cf(1)*u2)/mu;


gl3(2,2):=( - ((2*mu*u1 - rho*u3)*rho*u3 - (rho**3 + u1**2)*mu**2)*cf(1))/mu**2;


gl3(2,3):=((mu*u1 - rho*u3)*cf(1)*rho*u2)/mu**2;


gl3(3,1):=( - cf(1)*rho*u2**2)/mu;


gl3(3,2):=((mu*u1 - rho*u3)*cf(1)*rho*u2)/mu**2;


gl3(3,3):=(cf(1)*rho**2*u2**2)/mu**2;


;end;

