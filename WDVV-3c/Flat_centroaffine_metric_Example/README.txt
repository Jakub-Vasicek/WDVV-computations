In this directory we find a compatible pair of Hamiltonian operators for a 
special case of WDVV equation in N=3. 

Below we describe the files used for computations and what they each contain.

I. Finding the nonlocal first order operators for the case N=3

 1) nonloc_ho1.red
 -defining the metric of the operator using the Haantijes tensor

 2*) nonloc_ho1_res.red
 -there is the Haantijes metric saved

 3) nonloc_ho2.red 
 -trying to solve the equation \nabla_k V^i_j = \nabla_j V^k_i

 4*) nonloc_ho2_res.red
 -solution containing the metric of the 1st order operator

 5) nonloc_ho3.red 
 -solving the equation on the nonlocal tail coefficients 


II. Finding the local third order operator

 6) wdvv_3ord_op_CentroAff.red
 -finding the 3rd order operator

 7*) w3c_3ord_CentroAff_res.red
 -metric of the 3rd order operator


III. Using the previous results for proving the compatibilty

 8) wdvv_comp_nl2_CentroAff.red
 -Firstly computes the Schouten bracket of the non-local 1st order operator
  with itself and then with 3rd order local one

 9) wdvv_comp_nl1_CentroAff_res.red
 -result of the above

 10) riemann4.red
 -a library with many usefull pre-defined functions related to Riemaninan 
  geometry

Note: The library riemann4.red as well as most of the *res.red files have to be
present in the users working directory.

* these files are needed but not present as they are results of a previous 
  computations