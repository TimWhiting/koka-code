{
function processData(input) {
  let result = input;

  if (input > 10) {
    result = result * 2;  // Dead code, as input will always be 5
  } else {
    result = 0;
  }

  return result;
}

// Example usage
const processedValue = processData(5);
console.log("Processed value:", processedValue);
}


{
function transform(x) {
  return x
}
function processData(input) {
  let result = input;

  if (transform(input) > 10) {
    result = result * 2;  // Dead code, as input will always be 5
  } else {
    result = 0;
  }

  return result;
}

// Example usage
const processedValue = processData(5);
console.log("Processed value:", processedValue);
}

{
function processData(input, transform) {
  let result = input;

  if (transform(input) > 10) {
    result = result * 2;  // Dead code, as input will always be 5
  } else {
    result = 0;
  }

  return result;
}

// Example usage
const processedValue = processData(5, (x) => x);
console.log("Processed value:", processedValue);
}