#!/bin/bash

echo "Running Loventre Engine Tests..."
echo ""

source venv/bin/activate

# Run Python tests
echo "=== Python Unit Tests ==="
python -m pytest tests/ -v

echo ""
echo "=== Test Summary ==="
echo "All tests completed!"
deactivate
