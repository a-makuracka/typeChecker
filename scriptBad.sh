#!/bin/bash

INSC_LLVM="./insc"
TESTS_DIR="lattests/bad"

for test_file in "$TESTS_DIR"/bad*.lat; do
    test_name=$(basename "$test_file" .lat)
    input_path="$TESTS_DIR/$test_name.lat"

    # Execute your command with the test file and capture its output
    echo "Running test: $input_path"
    # Replace the echo command below with the command you want to run
    # Example: output=$("$INSC_LLVM" "$input_path")
    output=$("$INSC_LLVM" "$input_path")

    # Print the output of the command
    #echo "Output of test $test_name:"
    #echo "$output"
done
