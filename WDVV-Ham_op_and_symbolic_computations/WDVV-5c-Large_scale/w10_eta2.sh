#!/bin/bash
# sets home directory
DATADIR=$PATH_TO_DIRECTORY . "/Maple/w10_eta2_3ord_SC"


module add maple

cd $DATADIR
export OMP_NUM_THREADS=$PBS_NUM_PPN

maple <w10_eta2.txt >result.out
