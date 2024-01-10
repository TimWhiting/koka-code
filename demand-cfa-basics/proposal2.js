{
function processData(input) {
  let x = input * 2
  let y = input * 4
  return y;
}

// Example usage
console.log("Processed value:", processData(5));
}

{
function process(input, x) {
  return input * 4
}

function processData(input) {
  let x = input * 2
  let y = process(input, x)
  return y;
}

// Example usage
console.log("Processed value:", processData(5));
}

{
function processData(input, process) {
  let x = input * 2
  let y = process(input, x)
  return y;
}

// Example usage
console.log("Processed value:", processData(5, (x, y) => x + 3));
}


{
function process(obj, x){
  return obj.a + x
}
}

{
function process(a, x, alwaysThrows){
  alwaysThrows()
  return a + x
}
}

{
function addTo(list, value){
  return list.map((v) => v + value)
}
}