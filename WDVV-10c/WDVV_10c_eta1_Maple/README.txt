In this folder there are the programs, as well as their results, regarding the
computation of the third-order Hamiltonian operator for WDVV equation in N=5 
for Dubrovin's first normal form. The files contain the following:

 1) w10_hydro_system_gen.red
 -file for generating the WDVV system

 2) w10_eta_adiag_eq.red
 -this file contains the WDVV system as well as the hydrodynamic-type one

 3*) Jets.s
 -file containing the Maple extension for calculus in jet spaces

 4) w10_eta_adiag.mw
 -main file for the computation of the operator in Maple worksheet

 5) w10_eta_adiag.txt
 -only the plain text without output from the previous file

 6) w10_eta_adiag_result.txt
 -the metric of the operator in a "rough" form

 7) w10_eta_adiag_result_simplified.txt
 -pretty-printed the above matrix

Note: This computation had to be performed on a supercomputer with around 80GB
of RAM (CPU is not too important, computation is only memory demanding) and
around 5 days of computing. However, this can be avoided by not constructing
all 2100 equations but from experience the first 100 should be enough to 
determine all coefficients in the metric. Of course the solution can be checked
the same way and we should expect a one solution. Still it is preferred to use a
reasonably powerful machine.

*jets.s should be downloaded from the official software page: 
http://jets.math.slu.cz/
