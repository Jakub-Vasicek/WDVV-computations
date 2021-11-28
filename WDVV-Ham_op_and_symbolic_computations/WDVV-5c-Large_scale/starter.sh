#!/bin/bash
qsub -l select=1:ncpus=52:mem=256gb:scratch_local=1gb -l walltime=140:0:0 w10_eta2.sh