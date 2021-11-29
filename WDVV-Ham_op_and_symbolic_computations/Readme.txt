Files used in the paper are in the directory 
\WDVV-computations\WDVV-Ham_op_and_symbolic_computations

For computations in Reduce for N=3 files are all contained in the directory 
\WDVV-3c-Eta4
--Computing the first-order operator
The first step: 
Computation	dne3_loh2.red
Result		dne3_loh2_res.red
The second step:
Computation	dne3_loh3.red
Result		dne3_loh3_res.red
The third step:
Computation	dne3_loh4.red

--Computing the third-order operator
Computation	wdvv_3ord_op_eta4.red
Result		w3c_3ord_eta4_res.red

--Computing the compatibility of the above operators
[A1,A1]		wdvv_comp_nl1_eta4.red
Result		wdvv_comp_nl1_eta4_res.red

[A1,A3]		wdvv_comp_nl2_eta4.red
Result		wdvv_comp_nl2_eta4_res.red

--Accesory files
Segre matrix	w3c_3ord_eta4_res.mw
Riemann lib	riemann4.red


The file where we use jacobi.mpl is in \
--Computation of compatibility of the above operators in Maple using jacobi.mpl
[A1,A1],[A1,A3]		WDVV-3c-Compat_Example_Eta4.mw


Files for computation on supercomputer are in \WDVV-5c-Large_scale
--Files needed for the supercomputer
Starting script		starter.sh
Specific file script	w10_eta2.sh
Instructions for Maple	w10_eta2.txt
PDE system for input	w10_eta2_eq.red

--Accesory files
Maple WS		w10_eta2.mw
File for 
generating PDEs		w10_eta2.red
Result			w10_eta2_result.txt

