// Core Feature A: single loop-free method (★★)
method m(x: Int) {
    var y: Int := x + 15;
    match {
      x > 0 => 
        assert y/x > 0,
      true => 
        y := 5
    };
    assert y > 0
} //Passing


method m(x: Int): Int 
    requires x >= 0
    ensures result >= 0
    // false: (consider execution when x = 1)
    ensures result == 3 * x 
{
    var acc: Int := 0;
    acc := x / 2;
    acc := acc * 6;
    
    return acc
} //failing

// Core Feature B: partial correctness of loops (★★)
method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1) / 2
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= n
        invariant acc == i * (i + 1) / 2
    {
        i < n =>
            i := i + 1;
            acc := acc + i
    };
    assert i == n;
    assert acc == n * (n + 1) / 2;
    
    return acc
} // passing

method iter(n: Int): Int
    requires n >= 0
{
    var i: Int := 0;
    loop 
        // false: when the loop terminates, i == n + 1
        invariant i <= n 
    {
        i <= n => i := i + 1
    }
} // failing


// Core Feature C: error reporting (★★)
method sumn(n: Int): Int
    requires n >= 0
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        // Error: Invariant may not be preserved
        invariant i <= n 
    {
        i <= n =>
            acc := acc + i;
            i := i + 1
    };   
    return acc
} // failing

//Extension Feature 8: total correctness of loops (★★)
method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= n
        invariant acc == i * (i + 1) / 2
        decreases n - i
    {
        i < n =>
            i := i + 1;
            acc := acc + i
    };
    assert i == n;
    
    return acc;
    assert false
} //passing