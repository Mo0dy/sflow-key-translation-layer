#!/usr/bin/env sh

SFLOW_BIN=/home/felix/_Uni/BA/type-inference/inference-framework/checker-framework/checkers/binary
QUALS=/home/felix/_Uni/BA/type-inference/inference-framework/checker-framework/checkers/resources/edu/kit/translation/checkers
BASE_DIR=/home/felix/_Uni/BA/Java_Tests

$SFLOW_BIN/javai-sflow -Aqualspath="$QUALS" -Abasepath="$BASE_DIR" $BASE_DIR/*.java
