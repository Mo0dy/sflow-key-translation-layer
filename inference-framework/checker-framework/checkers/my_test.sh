#!/usr/bin/env sh

CHECKER_FRAMEWORK=/home/felix/_Uni/BA/type-inference/inference-framework/checker-framework
SFLOW_BIN="$CHECKER_FRAMEWORK/checkers/binary"
QUALS="$CHECKER_FRAMEWORK/checkers/resources/edu/kit/translation/checkers"
TESTS_DIR="$CHECKER_FRAMEWORK/checkers/tests/translation-layer"

$SFLOW_BIN/javai-sflow -Aqualspath="$QUALS" -Abasepath="$BASE_DIR" $TESTS_DIR/*.java
