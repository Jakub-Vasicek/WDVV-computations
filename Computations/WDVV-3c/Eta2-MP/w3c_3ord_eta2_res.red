
matrix gl3(3,3);


gl3(1,1):=(2*rho**2 - 2*rho*u2 + u2**2)*cf(1);


gl3(1,2):= - (rho*u3 - u1)*(rho - u2)*cf(1);


gl3(1,3):= - (rho - u2)**2*cf(1)*rho;


gl3(2,1):= - (rho*u3 - u1)*(rho - u2)*cf(1);


gl3(2,2):=(rho**3 + rho**2*u3**2 - 2*rho*u1*u3 + u1**2)*cf(1);


gl3(2,3):=(rho*u3 - u1)*(rho - u2)*cf(1)*rho;


gl3(3,1):= - (rho - u2)**2*cf(1)*rho;


gl3(3,2):=(rho*u3 - u1)*(rho - u2)*cf(1)*rho;


gl3(3,3):=(rho - u2)**2*cf(1)*rho**2;


cf(1):=1;


;end;

