
matrix gl3(3,3);


gl3(1,1):=cf(7)*u3**2;


gl3(1,2):= - cf(7);


gl3(1,3):= - cf(7)*u1*u3;


gl3(2,1):= - cf(7);


gl3(2,2):=0;


gl3(2,3):=0;


gl3(3,1):= - cf(7)*u1*u3;


gl3(3,2):=0;


gl3(3,3):=cf(7)*u1**2;


;end;

