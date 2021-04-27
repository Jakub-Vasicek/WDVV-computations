The above directories each contain example computations for normal forms 
(Dubrovin's or Mokhov-Pavlenko's) of the matrix eta. The structure, except for
a slight difference in the case eta1, is the same and in each we find a pair of
Hamiltonian operators and we check that they are indeed compatible. There is
also considered an example of flat centro-affine metric.

Below we describe the files used for computations and what they each contain.

I. Finding the nonlocal first order operators for the case N=3

In the folder ..\WDVV-3\etaX-xx\ there are all relevant files for finding
the operator of Ferapontov type for the case etaX. There are following files:

 1) dne3_lho2.red
 -defining the metric of the operator using the Haantijes tensor

 2) dne3_lho2_res.red
 -there is the Haantijes metric saved

 3) dne3_lho3.red 
 -trying to solve the equation \nabla_k V^i_j = \nabla_j V^k_i

 4) dne3_lho3_res.red
 -solution containing the metric of the 1st order operator

 5) dne3_lho4.red 
 -solving the equation on the nonlocal tail coefficients 

II. Finding the local third order operators for the case N=3

 6) wdvv_3ord_op_etaX.red
 -finding the 3rd order operator for case etaX

 7) w3c_3ord_etaX_res.red
 -metric of the 3rd order operator for case etaX

 8) w3c_3ord_etaX_res.mw
 -output for Maple to determine the Jordan form of the matrix S

III. Using the previous results for proving the compatibility

 9) wdvv_comp_nl1_etaX.red
 -Schouten bracket of the non-local 1st order operator with itself

 10) wdvv_comp_nl1_etaX_res.red
 -result of the above

 11) wdvv_comp_nl2_etaX.red
 -Schouten bracket of the non-local 1st order operator with 3rd order local one

 12) wdvv_comp_nl1_etaX_res.red
 -result of the above

 13) riemann4.red
 -a library with many useful pre-defined functions related to Riemannian 
  geometry

Note: The library riemann4.red as well as most of the *res.red files have to be
present in the users working directory.