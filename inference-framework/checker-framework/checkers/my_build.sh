#!/usr/bin/fish

source environment

ant bindist-nojdk && ./my_test.sh
