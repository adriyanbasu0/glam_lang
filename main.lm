// main.ox
// An example program in Ox Lang

// Declare a variable
let greeting = "Hello, Ox Lang!";
print greeting;

// Demonstrate immutability: create a new variable for the "updated" value
let count_initial = 10;
print "Initial count: ";
print count_initial;

let count_updated = count_initial + 5; // New variable for the updated value
print "Updated count: ";
print count_updated;

// Function definition
let add = fn(a, b) {
    return a + b;
};

// Call the function
let sum = add(10, 20);
print "Sum of 10 and 20: ";
print sum;

// Conditional statement
let number = 15;
if (number > 10) {
    print "Number is greater than 10";
} else {
    print "Number is not greater than 10";
}

// More complex expression
let result = (5 * (2 + 3)) - 10;
print "Result of (5 * (2 + 3)) - 10: ";
print result;

// Using boolean values
let is_ox_cool = true;
if (is_ox_cool) {
    print "Ox Lang is cool!";
} else {
    print "Ox Lang is not cool. (This should not print!)";
}

// Null value
let empty_var = null;
print "Value of empty_var: ";
print empty_var; // Should print 'null' or equivalent

// Another function with if-else
let factorial = fn(n) {
    if (n == 0) {
        return 1;
    } else {
        return n * factorial(n - 1);
    }
};

let fact_5 = factorial(5);
print "Factorial of 5: ";
print fact_5; // Should print 120
