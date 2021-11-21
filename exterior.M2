restart();
R = QQ[t0,t1,t2,SkewCommutative=>{0,1,2}];
I = ideal(t0 + t1 + t2, t0*t1 + t0*t2 + t1*t2, t0*t1*t2);
SC = R/I;
B = basis SC;


restart();
R = QQ[t0,t1,t2,t3,SkewCommutative=>{0,1,2,3}];
I = ideal(t0 + t1 + t2 + t3,
 t0*t1 + t0*t2 + t1*t2 + t0*t3 + t1*t3 + t2*t3,
 t0*t1*t2 + t0*t1*t3 + t0*t2*t3 + t1*t2*t3,
 t0*t1*t2*t3);
SC = R/I;
B = basis SC;


restart();
R = QQ[t0,t1,t2,t3,t4,SkewCommutative=>{0,1,2,3,4}];
I = ideal(t0 + t1 + t2 + t3 + t4,
 t0*t1 + t0*t2 + t1*t2 + t0*t3 + t1*t3 + t2*t3 + t0*t4 + t1*t4 + t2*t4 + t3*t4,
 t0*t1*t2 + t0*t1*t3 + t0*t2*t3 + t1*t2*t3 + t0*t1*t4 + t0*t2*t4 + t1*t2*t4 + t0*t3*t4 + t1*t3*t4 + t2*t3*t4,
 t0*t1*t2*t3 + t0*t1*t2*t4 + t0*t1*t3*t4 + t0*t2*t3*t4 + t1*t2*t3*t4,
 t0*t1*t2*t3*t4);
SC = R/I;
B = basis SC;

restart();
R = QQ[t0,t1,t2,t3,t4,t5,SkewCommutative=>{0,1,2,3,4,5}];
I = ideal(t0 + t1 + t2 + t3 + t4 + t5,
 t0*t1 + t0*t2 + t1*t2 + t0*t3 + t1*t3 + t2*t3 + t0*t4 + t1*t4 + t2*t4 + t3*t4 + t0*t5 + t1*t5 + t2*t5 + t3*t5 + t4*t5,
 t0*t1*t2 + t0*t1*t3 + t0*t2*t3 + t1*t2*t3 + t0*t1*t4 + t0*t2*t4 + t1*t2*t4 + t0*t3*t4 + t1*t3*t4 + t2*t3*t4 + t0*t1*t5 + t0*t2*t5 + t1*t2*t5 + t0*t3*t5 + t1*t3*t5 + t2*t3*t5 + t0*t4*t5 + t1*t4*t5 + t2*t4*t5 + t3*t4*t5,
 t0*t1*t2*t3 + t0*t1*t2*t4 + t0*t1*t3*t4 + t0*t2*t3*t4 + t1*t2*t3*t4 + t0*t1*t2*t5 + t0*t1*t3*t5 + t0*t2*t3*t5 + t1*t2*t3*t5 + t0*t1*t4*t5 + t0*t2*t4*t5 + t1*t2*t4*t5 + t0*t3*t4*t5 + t1*t3*t4*t5 + t2*t3*t4*t5,
 t0*t1*t2*t3*t4 + t0*t1*t2*t3*t5 + t0*t1*t2*t4*t5 + t0*t1*t3*t4*t5 + t0*t2*t3*t4*t5 + t1*t2*t3*t4*t5,
 t0*t1*t2*t3*t4*t5);
SC = R/I;
B = basis SC;

restart();
R = QQ[t0,t1,t2,t3,t4,t5,t6,SkewCommutative=>{0,1,2,3,4,5,6}];
I = ideal(t0 + t1 + t2 + t3 + t4 + t5 + t6,
 t0*t1 + t0*t2 + t1*t2 + t0*t3 + t1*t3 + t2*t3 + t0*t4 + t1*t4 + t2*t4 + t3*t4 + t0*t5 + t1*t5 + t2*t5 + t3*t5 + t4*t5 + t0*t6 + t1*t6 + t2*t6 + t3*t6 + t4*t6 + t5*t6,
 t0*t1*t2 + t0*t1*t3 + t0*t2*t3 + t1*t2*t3 + t0*t1*t4 + t0*t2*t4 + t1*t2*t4 + t0*t3*t4 + t1*t3*t4 + t2*t3*t4 + t0*t1*t5 + t0*t2*t5 + t1*t2*t5 + t0*t3*t5 + t1*t3*t5 + t2*t3*t5 + t0*t4*t5 + t1*t4*t5 + t2*t4*t5 + t3*t4*t5 + t0*t1*t6 + t0*t2*t6 + t1*t2*t6 + t0*t3*t6 + t1*t3*t6 + t2*t3*t6 + t0*t4*t6 + t1*t4*t6 + t2*t4*t6 + t3*t4*t6 + t0*t5*t6 + t1*t5*t6 + t2*t5*t6 + t3*t5*t6 + t4*t5*t6,
 t0*t1*t2*t3 + t0*t1*t2*t4 + t0*t1*t3*t4 + t0*t2*t3*t4 + t1*t2*t3*t4 + t0*t1*t2*t5 + t0*t1*t3*t5 + t0*t2*t3*t5 + t1*t2*t3*t5 + t0*t1*t4*t5 + t0*t2*t4*t5 + t1*t2*t4*t5 + t0*t3*t4*t5 + t1*t3*t4*t5 + t2*t3*t4*t5 + t0*t1*t2*t6 + t0*t1*t3*t6 + t0*t2*t3*t6 + t1*t2*t3*t6 + t0*t1*t4*t6 + t0*t2*t4*t6 + t1*t2*t4*t6 + t0*t3*t4*t6 + t1*t3*t4*t6 + t2*t3*t4*t6 + t0*t1*t5*t6 + t0*t2*t5*t6 + t1*t2*t5*t6 + t0*t3*t5*t6 + t1*t3*t5*t6 + t2*t3*t5*t6 + t0*t4*t5*t6 + t1*t4*t5*t6 + t2*t4*t5*t6 + t3*t4*t5*t6,
 t0*t1*t2*t3*t4 + t0*t1*t2*t3*t5 + t0*t1*t2*t4*t5 + t0*t1*t3*t4*t5 + t0*t2*t3*t4*t5 + t1*t2*t3*t4*t5 + t0*t1*t2*t3*t6 + t0*t1*t2*t4*t6 + t0*t1*t3*t4*t6 + t0*t2*t3*t4*t6 + t1*t2*t3*t4*t6 + t0*t1*t2*t5*t6 + t0*t1*t3*t5*t6 + t0*t2*t3*t5*t6 + t1*t2*t3*t5*t6 + t0*t1*t4*t5*t6 + t0*t2*t4*t5*t6 + t1*t2*t4*t5*t6 + t0*t3*t4*t5*t6 + t1*t3*t4*t5*t6 + t2*t3*t4*t5*t6,
 t0*t1*t2*t3*t4*t5 + t0*t1*t2*t3*t4*t6 + t0*t1*t2*t3*t5*t6 + t0*t1*t2*t4*t5*t6 + t0*t1*t3*t4*t5*t6 + t0*t2*t3*t4*t5*t6 + t1*t2*t3*t4*t5*t6,
 t0*t1*t2*t3*t4*t5*t6);
SC = R/I;
B = basis SC;

restart();
R = QQ[t0,t1,t2,t3,t4,t5,t6,t7,SkewCommutative=>{0,1,2,3,4,5,6,7}];
I = ideal(t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7,
 t0*t1 + t0*t2 + t1*t2 + t0*t3 + t1*t3 + t2*t3 + t0*t4 + t1*t4 + t2*t4 + t3*t4 + t0*t5 + t1*t5 + t2*t5 + t3*t5 + t4*t5 + t0*t6 + t1*t6 + t2*t6 + t3*t6 + t4*t6 + t5*t6 + t0*t7 + t1*t7 + t2*t7 + t3*t7 + t4*t7 + t5*t7 + t6*t7,
 t0*t1*t2 + t0*t1*t3 + t0*t2*t3 + t1*t2*t3 + t0*t1*t4 + t0*t2*t4 + t1*t2*t4 + t0*t3*t4 + t1*t3*t4 + t2*t3*t4 + t0*t1*t5 + t0*t2*t5 + t1*t2*t5 + t0*t3*t5 + t1*t3*t5 + t2*t3*t5 + t0*t4*t5 + t1*t4*t5 + t2*t4*t5 + t3*t4*t5 + t0*t1*t6 + t0*t2*t6 + t1*t2*t6 + t0*t3*t6 + t1*t3*t6 + t2*t3*t6 + t0*t4*t6 + t1*t4*t6 + t2*t4*t6 + t3*t4*t6 + t0*t5*t6 + t1*t5*t6 + t2*t5*t6 + t3*t5*t6 + t4*t5*t6 + t0*t1*t7 + t0*t2*t7 + t1*t2*t7 + t0*t3*t7 + t1*t3*t7 + t2*t3*t7 + t0*t4*t7 + t1*t4*t7 + t2*t4*t7 + t3*t4*t7 + t0*t5*t7 + t1*t5*t7 + t2*t5*t7 + t3*t5*t7 + t4*t5*t7 + t0*t6*t7 + t1*t6*t7 + t2*t6*t7 + t3*t6*t7 + t4*t6*t7 + t5*t6*t7,
 t0*t1*t2*t3 + t0*t1*t2*t4 + t0*t1*t3*t4 + t0*t2*t3*t4 + t1*t2*t3*t4 + t0*t1*t2*t5 + t0*t1*t3*t5 + t0*t2*t3*t5 + t1*t2*t3*t5 + t0*t1*t4*t5 + t0*t2*t4*t5 + t1*t2*t4*t5 + t0*t3*t4*t5 + t1*t3*t4*t5 + t2*t3*t4*t5 + t0*t1*t2*t6 + t0*t1*t3*t6 + t0*t2*t3*t6 + t1*t2*t3*t6 + t0*t1*t4*t6 + t0*t2*t4*t6 + t1*t2*t4*t6 + t0*t3*t4*t6 + t1*t3*t4*t6 + t2*t3*t4*t6 + t0*t1*t5*t6 + t0*t2*t5*t6 + t1*t2*t5*t6 + t0*t3*t5*t6 + t1*t3*t5*t6 + t2*t3*t5*t6 + t0*t4*t5*t6 + t1*t4*t5*t6 + t2*t4*t5*t6 + t3*t4*t5*t6 + t0*t1*t2*t7 + t0*t1*t3*t7 + t0*t2*t3*t7 + t1*t2*t3*t7 + t0*t1*t4*t7 + t0*t2*t4*t7 + t1*t2*t4*t7 + t0*t3*t4*t7 + t1*t3*t4*t7 + t2*t3*t4*t7 + t0*t1*t5*t7 + t0*t2*t5*t7 + t1*t2*t5*t7 + t0*t3*t5*t7 + t1*t3*t5*t7 + t2*t3*t5*t7 + t0*t4*t5*t7 + t1*t4*t5*t7 + t2*t4*t5*t7 + t3*t4*t5*t7 + t0*t1*t6*t7 + t0*t2*t6*t7 + t1*t2*t6*t7 + t0*t3*t6*t7 + t1*t3*t6*t7 + t2*t3*t6*t7 + t0*t4*t6*t7 + t1*t4*t6*t7 + t2*t4*t6*t7 + t3*t4*t6*t7 + t0*t5*t6*t7 + t1*t5*t6*t7 + t2*t5*t6*t7 + t3*t5*t6*t7 + t4*t5*t6*t7,
 t0*t1*t2*t3*t4 + t0*t1*t2*t3*t5 + t0*t1*t2*t4*t5 + t0*t1*t3*t4*t5 + t0*t2*t3*t4*t5 + t1*t2*t3*t4*t5 + t0*t1*t2*t3*t6 + t0*t1*t2*t4*t6 + t0*t1*t3*t4*t6 + t0*t2*t3*t4*t6 + t1*t2*t3*t4*t6 + t0*t1*t2*t5*t6 + t0*t1*t3*t5*t6 + t0*t2*t3*t5*t6 + t1*t2*t3*t5*t6 + t0*t1*t4*t5*t6 + t0*t2*t4*t5*t6 + t1*t2*t4*t5*t6 + t0*t3*t4*t5*t6 + t1*t3*t4*t5*t6 + t2*t3*t4*t5*t6 + t0*t1*t2*t3*t7 + t0*t1*t2*t4*t7 + t0*t1*t3*t4*t7 + t0*t2*t3*t4*t7 + t1*t2*t3*t4*t7 + t0*t1*t2*t5*t7 + t0*t1*t3*t5*t7 + t0*t2*t3*t5*t7 + t1*t2*t3*t5*t7 + t0*t1*t4*t5*t7 + t0*t2*t4*t5*t7 + t1*t2*t4*t5*t7 + t0*t3*t4*t5*t7 + t1*t3*t4*t5*t7 + t2*t3*t4*t5*t7 + t0*t1*t2*t6*t7 + t0*t1*t3*t6*t7 + t0*t2*t3*t6*t7 + t1*t2*t3*t6*t7 + t0*t1*t4*t6*t7 + t0*t2*t4*t6*t7 + t1*t2*t4*t6*t7 + t0*t3*t4*t6*t7 + t1*t3*t4*t6*t7 + t2*t3*t4*t6*t7 + t0*t1*t5*t6*t7 + t0*t2*t5*t6*t7 + t1*t2*t5*t6*t7 + t0*t3*t5*t6*t7 + t1*t3*t5*t6*t7 + t2*t3*t5*t6*t7 + t0*t4*t5*t6*t7 + t1*t4*t5*t6*t7 + t2*t4*t5*t6*t7 + t3*t4*t5*t6*t7,
 t0*t1*t2*t3*t4*t5 + t0*t1*t2*t3*t4*t6 + t0*t1*t2*t3*t5*t6 + t0*t1*t2*t4*t5*t6 + t0*t1*t3*t4*t5*t6 + t0*t2*t3*t4*t5*t6 + t1*t2*t3*t4*t5*t6 + t0*t1*t2*t3*t4*t7 + t0*t1*t2*t3*t5*t7 + t0*t1*t2*t4*t5*t7 + t0*t1*t3*t4*t5*t7 + t0*t2*t3*t4*t5*t7 + t1*t2*t3*t4*t5*t7 + t0*t1*t2*t3*t6*t7 + t0*t1*t2*t4*t6*t7 + t0*t1*t3*t4*t6*t7 + t0*t2*t3*t4*t6*t7 + t1*t2*t3*t4*t6*t7 + t0*t1*t2*t5*t6*t7 + t0*t1*t3*t5*t6*t7 + t0*t2*t3*t5*t6*t7 + t1*t2*t3*t5*t6*t7 + t0*t1*t4*t5*t6*t7 + t0*t2*t4*t5*t6*t7 + t1*t2*t4*t5*t6*t7 + t0*t3*t4*t5*t6*t7 + t1*t3*t4*t5*t6*t7 + t2*t3*t4*t5*t6*t7,
 t0*t1*t2*t3*t4*t5*t6 + t0*t1*t2*t3*t4*t5*t7 + t0*t1*t2*t3*t4*t6*t7 + t0*t1*t2*t3*t5*t6*t7 + t0*t1*t2*t4*t5*t6*t7 + t0*t1*t3*t4*t5*t6*t7 + t0*t2*t3*t4*t5*t6*t7 + t1*t2*t3*t4*t5*t6*t7,
 t0*t1*t2*t3*t4*t5*t6*t7);
SC = R/I;
B = basis SC;

restart();
R = QQ[t0,t1,t2,t3,t4,t5,t6,t7,t8,SkewCommutative=>{0,1,2,3,4,5,6,7,8}];
I = ideal(t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8,
 t0*t1 + t0*t2 + t1*t2 + t0*t3 + t1*t3 + t2*t3 + t0*t4 + t1*t4 + t2*t4 + t3*t4 + t0*t5 + t1*t5 + t2*t5 + t3*t5 + t4*t5 + t0*t6 + t1*t6 + t2*t6 + t3*t6 + t4*t6 + t5*t6 + t0*t7 + t1*t7 + t2*t7 + t3*t7 + t4*t7 + t5*t7 + t6*t7 + t0*t8 + t1*t8 + t2*t8 + t3*t8 + t4*t8 + t5*t8 + t6*t8 + t7*t8,
 t0*t1*t2 + t0*t1*t3 + t0*t2*t3 + t1*t2*t3 + t0*t1*t4 + t0*t2*t4 + t1*t2*t4 + t0*t3*t4 + t1*t3*t4 + t2*t3*t4 + t0*t1*t5 + t0*t2*t5 + t1*t2*t5 + t0*t3*t5 + t1*t3*t5 + t2*t3*t5 + t0*t4*t5 + t1*t4*t5 + t2*t4*t5 + t3*t4*t5 + t0*t1*t6 + t0*t2*t6 + t1*t2*t6 + t0*t3*t6 + t1*t3*t6 + t2*t3*t6 + t0*t4*t6 + t1*t4*t6 + t2*t4*t6 + t3*t4*t6 + t0*t5*t6 + t1*t5*t6 + t2*t5*t6 + t3*t5*t6 + t4*t5*t6 + t0*t1*t7 + t0*t2*t7 + t1*t2*t7 + t0*t3*t7 + t1*t3*t7 + t2*t3*t7 + t0*t4*t7 + t1*t4*t7 + t2*t4*t7 + t3*t4*t7 + t0*t5*t7 + t1*t5*t7 + t2*t5*t7 + t3*t5*t7 + t4*t5*t7 + t0*t6*t7 + t1*t6*t7 + t2*t6*t7 + t3*t6*t7 + t4*t6*t7 + t5*t6*t7 + t0*t1*t8 + t0*t2*t8 + t1*t2*t8 + t0*t3*t8 + t1*t3*t8 + t2*t3*t8 + t0*t4*t8 + t1*t4*t8 + t2*t4*t8 + t3*t4*t8 + t0*t5*t8 + t1*t5*t8 + t2*t5*t8 + t3*t5*t8 + t4*t5*t8 + t0*t6*t8 + t1*t6*t8 + t2*t6*t8 + t3*t6*t8 + t4*t6*t8 + t5*t6*t8 + t0*t7*t8 + t1*t7*t8 + t2*t7*t8 + t3*t7*t8 + t4*t7*t8 + t5*t7*t8 + t6*t7*t8,
 t0*t1*t2*t3 + t0*t1*t2*t4 + t0*t1*t3*t4 + t0*t2*t3*t4 + t1*t2*t3*t4 + t0*t1*t2*t5 + t0*t1*t3*t5 + t0*t2*t3*t5 + t1*t2*t3*t5 + t0*t1*t4*t5 + t0*t2*t4*t5 + t1*t2*t4*t5 + t0*t3*t4*t5 + t1*t3*t4*t5 + t2*t3*t4*t5 + t0*t1*t2*t6 + t0*t1*t3*t6 + t0*t2*t3*t6 + t1*t2*t3*t6 + t0*t1*t4*t6 + t0*t2*t4*t6 + t1*t2*t4*t6 + t0*t3*t4*t6 + t1*t3*t4*t6 + t2*t3*t4*t6 + t0*t1*t5*t6 + t0*t2*t5*t6 + t1*t2*t5*t6 + t0*t3*t5*t6 + t1*t3*t5*t6 + t2*t3*t5*t6 + t0*t4*t5*t6 + t1*t4*t5*t6 + t2*t4*t5*t6 + t3*t4*t5*t6 + t0*t1*t2*t7 + t0*t1*t3*t7 + t0*t2*t3*t7 + t1*t2*t3*t7 + t0*t1*t4*t7 + t0*t2*t4*t7 + t1*t2*t4*t7 + t0*t3*t4*t7 + t1*t3*t4*t7 + t2*t3*t4*t7 + t0*t1*t5*t7 + t0*t2*t5*t7 + t1*t2*t5*t7 + t0*t3*t5*t7 + t1*t3*t5*t7 + t2*t3*t5*t7 + t0*t4*t5*t7 + t1*t4*t5*t7 + t2*t4*t5*t7 + t3*t4*t5*t7 + t0*t1*t6*t7 + t0*t2*t6*t7 + t1*t2*t6*t7 + t0*t3*t6*t7 + t1*t3*t6*t7 + t2*t3*t6*t7 + t0*t4*t6*t7 + t1*t4*t6*t7 + t2*t4*t6*t7 + t3*t4*t6*t7 + t0*t5*t6*t7 + t1*t5*t6*t7 + t2*t5*t6*t7 + t3*t5*t6*t7 + t4*t5*t6*t7 + t0*t1*t2*t8 + t0*t1*t3*t8 + t0*t2*t3*t8 + t1*t2*t3*t8 + t0*t1*t4*t8 + t0*t2*t4*t8 + t1*t2*t4*t8 + t0*t3*t4*t8 + t1*t3*t4*t8 + t2*t3*t4*t8 + t0*t1*t5*t8 + t0*t2*t5*t8 + t1*t2*t5*t8 + t0*t3*t5*t8 + t1*t3*t5*t8 + t2*t3*t5*t8 + t0*t4*t5*t8 + t1*t4*t5*t8 + t2*t4*t5*t8 + t3*t4*t5*t8 + t0*t1*t6*t8 + t0*t2*t6*t8 + t1*t2*t6*t8 + t0*t3*t6*t8 + t1*t3*t6*t8 + t2*t3*t6*t8 + t0*t4*t6*t8 + t1*t4*t6*t8 + t2*t4*t6*t8 + t3*t4*t6*t8 + t0*t5*t6*t8 + t1*t5*t6*t8 + t2*t5*t6*t8 + t3*t5*t6*t8 + t4*t5*t6*t8 + t0*t1*t7*t8 + t0*t2*t7*t8 + t1*t2*t7*t8 + t0*t3*t7*t8 + t1*t3*t7*t8 + t2*t3*t7*t8 + t0*t4*t7*t8 + t1*t4*t7*t8 + t2*t4*t7*t8 + t3*t4*t7*t8 + t0*t5*t7*t8 + t1*t5*t7*t8 + t2*t5*t7*t8 + t3*t5*t7*t8 + t4*t5*t7*t8 + t0*t6*t7*t8 + t1*t6*t7*t8 + t2*t6*t7*t8 + t3*t6*t7*t8 + t4*t6*t7*t8 + t5*t6*t7*t8,
 t0*t1*t2*t3*t4 + t0*t1*t2*t3*t5 + t0*t1*t2*t4*t5 + t0*t1*t3*t4*t5 + t0*t2*t3*t4*t5 + t1*t2*t3*t4*t5 + t0*t1*t2*t3*t6 + t0*t1*t2*t4*t6 + t0*t1*t3*t4*t6 + t0*t2*t3*t4*t6 + t1*t2*t3*t4*t6 + t0*t1*t2*t5*t6 + t0*t1*t3*t5*t6 + t0*t2*t3*t5*t6 + t1*t2*t3*t5*t6 + t0*t1*t4*t5*t6 + t0*t2*t4*t5*t6 + t1*t2*t4*t5*t6 + t0*t3*t4*t5*t6 + t1*t3*t4*t5*t6 + t2*t3*t4*t5*t6 + t0*t1*t2*t3*t7 + t0*t1*t2*t4*t7 + t0*t1*t3*t4*t7 + t0*t2*t3*t4*t7 + t1*t2*t3*t4*t7 + t0*t1*t2*t5*t7 + t0*t1*t3*t5*t7 + t0*t2*t3*t5*t7 + t1*t2*t3*t5*t7 + t0*t1*t4*t5*t7 + t0*t2*t4*t5*t7 + t1*t2*t4*t5*t7 + t0*t3*t4*t5*t7 + t1*t3*t4*t5*t7 + t2*t3*t4*t5*t7 + t0*t1*t2*t6*t7 + t0*t1*t3*t6*t7 + t0*t2*t3*t6*t7 + t1*t2*t3*t6*t7 + t0*t1*t4*t6*t7 + t0*t2*t4*t6*t7 + t1*t2*t4*t6*t7 + t0*t3*t4*t6*t7 + t1*t3*t4*t6*t7 + t2*t3*t4*t6*t7 + t0*t1*t5*t6*t7 + t0*t2*t5*t6*t7 + t1*t2*t5*t6*t7 + t0*t3*t5*t6*t7 + t1*t3*t5*t6*t7 + t2*t3*t5*t6*t7 + t0*t4*t5*t6*t7 + t1*t4*t5*t6*t7 + t2*t4*t5*t6*t7 + t3*t4*t5*t6*t7 + t0*t1*t2*t3*t8 + t0*t1*t2*t4*t8 + t0*t1*t3*t4*t8 + t0*t2*t3*t4*t8 + t1*t2*t3*t4*t8 + t0*t1*t2*t5*t8 + t0*t1*t3*t5*t8 + t0*t2*t3*t5*t8 + t1*t2*t3*t5*t8 + t0*t1*t4*t5*t8 + t0*t2*t4*t5*t8 + t1*t2*t4*t5*t8 + t0*t3*t4*t5*t8 + t1*t3*t4*t5*t8 + t2*t3*t4*t5*t8 + t0*t1*t2*t6*t8 + t0*t1*t3*t6*t8 + t0*t2*t3*t6*t8 + t1*t2*t3*t6*t8 + t0*t1*t4*t6*t8 + t0*t2*t4*t6*t8 + t1*t2*t4*t6*t8 + t0*t3*t4*t6*t8 + t1*t3*t4*t6*t8 + t2*t3*t4*t6*t8 + t0*t1*t5*t6*t8 + t0*t2*t5*t6*t8 + t1*t2*t5*t6*t8 + t0*t3*t5*t6*t8 + t1*t3*t5*t6*t8 + t2*t3*t5*t6*t8 + t0*t4*t5*t6*t8 + t1*t4*t5*t6*t8 + t2*t4*t5*t6*t8 + t3*t4*t5*t6*t8 + t0*t1*t2*t7*t8 + t0*t1*t3*t7*t8 + t0*t2*t3*t7*t8 + t1*t2*t3*t7*t8 + t0*t1*t4*t7*t8 + t0*t2*t4*t7*t8 + t1*t2*t4*t7*t8 + t0*t3*t4*t7*t8 + t1*t3*t4*t7*t8 + t2*t3*t4*t7*t8 + t0*t1*t5*t7*t8 + t0*t2*t5*t7*t8 + t1*t2*t5*t7*t8 + t0*t3*t5*t7*t8 + t1*t3*t5*t7*t8 + t2*t3*t5*t7*t8 + t0*t4*t5*t7*t8 + t1*t4*t5*t7*t8 + t2*t4*t5*t7*t8 + t3*t4*t5*t7*t8 + t0*t1*t6*t7*t8 + t0*t2*t6*t7*t8 + t1*t2*t6*t7*t8 + t0*t3*t6*t7*t8 + t1*t3*t6*t7*t8 + t2*t3*t6*t7*t8 + t0*t4*t6*t7*t8 + t1*t4*t6*t7*t8 + t2*t4*t6*t7*t8 + t3*t4*t6*t7*t8 + t0*t5*t6*t7*t8 + t1*t5*t6*t7*t8 + t2*t5*t6*t7*t8 + t3*t5*t6*t7*t8 + t4*t5*t6*t7*t8,
 t0*t1*t2*t3*t4*t5 + t0*t1*t2*t3*t4*t6 + t0*t1*t2*t3*t5*t6 + t0*t1*t2*t4*t5*t6 + t0*t1*t3*t4*t5*t6 + t0*t2*t3*t4*t5*t6 + t1*t2*t3*t4*t5*t6 + t0*t1*t2*t3*t4*t7 + t0*t1*t2*t3*t5*t7 + t0*t1*t2*t4*t5*t7 + t0*t1*t3*t4*t5*t7 + t0*t2*t3*t4*t5*t7 + t1*t2*t3*t4*t5*t7 + t0*t1*t2*t3*t6*t7 + t0*t1*t2*t4*t6*t7 + t0*t1*t3*t4*t6*t7 + t0*t2*t3*t4*t6*t7 + t1*t2*t3*t4*t6*t7 + t0*t1*t2*t5*t6*t7 + t0*t1*t3*t5*t6*t7 + t0*t2*t3*t5*t6*t7 + t1*t2*t3*t5*t6*t7 + t0*t1*t4*t5*t6*t7 + t0*t2*t4*t5*t6*t7 + t1*t2*t4*t5*t6*t7 + t0*t3*t4*t5*t6*t7 + t1*t3*t4*t5*t6*t7 + t2*t3*t4*t5*t6*t7 + t0*t1*t2*t3*t4*t8 + t0*t1*t2*t3*t5*t8 + t0*t1*t2*t4*t5*t8 + t0*t1*t3*t4*t5*t8 + t0*t2*t3*t4*t5*t8 + t1*t2*t3*t4*t5*t8 + t0*t1*t2*t3*t6*t8 + t0*t1*t2*t4*t6*t8 + t0*t1*t3*t4*t6*t8 + t0*t2*t3*t4*t6*t8 + t1*t2*t3*t4*t6*t8 + t0*t1*t2*t5*t6*t8 + t0*t1*t3*t5*t6*t8 + t0*t2*t3*t5*t6*t8 + t1*t2*t3*t5*t6*t8 + t0*t1*t4*t5*t6*t8 + t0*t2*t4*t5*t6*t8 + t1*t2*t4*t5*t6*t8 + t0*t3*t4*t5*t6*t8 + t1*t3*t4*t5*t6*t8 + t2*t3*t4*t5*t6*t8 + t0*t1*t2*t3*t7*t8 + t0*t1*t2*t4*t7*t8 + t0*t1*t3*t4*t7*t8 + t0*t2*t3*t4*t7*t8 + t1*t2*t3*t4*t7*t8 + t0*t1*t2*t5*t7*t8 + t0*t1*t3*t5*t7*t8 + t0*t2*t3*t5*t7*t8 + t1*t2*t3*t5*t7*t8 + t0*t1*t4*t5*t7*t8 + t0*t2*t4*t5*t7*t8 + t1*t2*t4*t5*t7*t8 + t0*t3*t4*t5*t7*t8 + t1*t3*t4*t5*t7*t8 + t2*t3*t4*t5*t7*t8 + t0*t1*t2*t6*t7*t8 + t0*t1*t3*t6*t7*t8 + t0*t2*t3*t6*t7*t8 + t1*t2*t3*t6*t7*t8 + t0*t1*t4*t6*t7*t8 + t0*t2*t4*t6*t7*t8 + t1*t2*t4*t6*t7*t8 + t0*t3*t4*t6*t7*t8 + t1*t3*t4*t6*t7*t8 + t2*t3*t4*t6*t7*t8 + t0*t1*t5*t6*t7*t8 + t0*t2*t5*t6*t7*t8 + t1*t2*t5*t6*t7*t8 + t0*t3*t5*t6*t7*t8 + t1*t3*t5*t6*t7*t8 + t2*t3*t5*t6*t7*t8 + t0*t4*t5*t6*t7*t8 + t1*t4*t5*t6*t7*t8 + t2*t4*t5*t6*t7*t8 + t3*t4*t5*t6*t7*t8,
 t0*t1*t2*t3*t4*t5*t6 + t0*t1*t2*t3*t4*t5*t7 + t0*t1*t2*t3*t4*t6*t7 + t0*t1*t2*t3*t5*t6*t7 + t0*t1*t2*t4*t5*t6*t7 + t0*t1*t3*t4*t5*t6*t7 + t0*t2*t3*t4*t5*t6*t7 + t1*t2*t3*t4*t5*t6*t7 + t0*t1*t2*t3*t4*t5*t8 + t0*t1*t2*t3*t4*t6*t8 + t0*t1*t2*t3*t5*t6*t8 + t0*t1*t2*t4*t5*t6*t8 + t0*t1*t3*t4*t5*t6*t8 + t0*t2*t3*t4*t5*t6*t8 + t1*t2*t3*t4*t5*t6*t8 + t0*t1*t2*t3*t4*t7*t8 + t0*t1*t2*t3*t5*t7*t8 + t0*t1*t2*t4*t5*t7*t8 + t0*t1*t3*t4*t5*t7*t8 + t0*t2*t3*t4*t5*t7*t8 + t1*t2*t3*t4*t5*t7*t8 + t0*t1*t2*t3*t6*t7*t8 + t0*t1*t2*t4*t6*t7*t8 + t0*t1*t3*t4*t6*t7*t8 + t0*t2*t3*t4*t6*t7*t8 + t1*t2*t3*t4*t6*t7*t8 + t0*t1*t2*t5*t6*t7*t8 + t0*t1*t3*t5*t6*t7*t8 + t0*t2*t3*t5*t6*t7*t8 + t1*t2*t3*t5*t6*t7*t8 + t0*t1*t4*t5*t6*t7*t8 + t0*t2*t4*t5*t6*t7*t8 + t1*t2*t4*t5*t6*t7*t8 + t0*t3*t4*t5*t6*t7*t8 + t1*t3*t4*t5*t6*t7*t8 + t2*t3*t4*t5*t6*t7*t8,
 t0*t1*t2*t3*t4*t5*t6*t7 + t0*t1*t2*t3*t4*t5*t6*t8 + t0*t1*t2*t3*t4*t5*t7*t8 + t0*t1*t2*t3*t4*t6*t7*t8 + t0*t1*t2*t3*t5*t6*t7*t8 + t0*t1*t2*t4*t5*t6*t7*t8 + t0*t1*t3*t4*t5*t6*t7*t8 + t0*t2*t3*t4*t5*t6*t7*t8 + t1*t2*t3*t4*t5*t6*t7*t8,
 t0*t1*t2*t3*t4*t5*t6*t7*t8);
SC = R/I;
B = basis SC;
