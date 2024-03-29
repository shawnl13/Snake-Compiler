
#[repr(C)]
#[derive(PartialEq, Eq, Copy, Clone)]
struct SnakeVal(u64);

#[repr(C)]
struct SnakeArray {
    size: u64,
    elts: *const SnakeVal,
}

/* You can use this function to cast a pointer to an array on the heap
 * into something more convenient to access
 *
 */
fn load_snake_array(p: *const u64) -> SnakeArray {
    unsafe {
        let size = *p;
        SnakeArray {
            size,
            elts: std::mem::transmute(p.add(1)),
        }
    }
}

static INT_TAG: u64 = 0x00_00_00_00_00_00_00_01;
static SNAKE_TRU: SnakeVal = SnakeVal(0xFF_FF_FF_FF_FF_FF_FF_FF);
static SNAKE_FLS: SnakeVal = SnakeVal(0x7F_FF_FF_FF_FF_FF_FF_FF);


#[link(name = "compiled_code", kind = "static")]
extern "sysv64" {

    // The \x01 here is an undocumented feature of LLVM that ensures
    // it does not add an underscore in front of the name.
    #[link_name = "\x01start_here"]
    fn start_here() -> SnakeVal;
}

// reinterprets the bytes of an unsigned number to a signed number
fn unsigned_to_signed(x: u64) -> i64 {
    i64::from_le_bytes(x.to_le_bytes())
}

fn sprint_snake_val(x: SnakeVal, mut seen_arrays: Vec<u64>) -> String {
   // println!("Entering sprint_snake_val with: {}", x.0);

    let mut output = "".to_string();
    if x.0 & INT_TAG == 0 {
        // it's a number
        format!("{}", unsigned_to_signed(x.0) >> 1)
    } else if x == SNAKE_TRU {
        String::from("true")
    } else if x == SNAKE_FLS {
        String::from("false")
    } else if x.0 & 7 == 1 { // array
        //println!("Printing an array");
        unsafe{
            if seen_arrays.contains(&x.0) { return "<loop>".to_string(); }
            seen_arrays.push(x.0);
            let snake_array = load_snake_array(std::mem::transmute(x.0-1));
            let length = snake_array.size as usize;
            let p = snake_array.elts; // points to the first element of array
            let mut i = 0 as usize;
            output += "[";
            while i < length{
                //let e:SnakeVal = *p;//std::mem::transmute::<*const SnakeVal>(p);// store thing that p points to
                
                output += &sprint_snake_val(*p.add(i), seen_arrays.clone());
                if i+1<length {output += ", ";}
                i += 1;
            }
            output += "]";
            
            

            /* 
            let pair = [ 0 , 1 ] in
            pair[1] := pair;
            pair
            should print: "[0, <loop>]"


            let pair = [ 0 , 1 ] in
            let second = [pair, pair] in
            second
            should print: "[[0, 1], [0, 1]]""        */
            

            return output;
        }
    } else if x.0 & 7 == 3 { // closure
        return "<closure>".to_string();
    } else {
        format!("Invalid snake value 0x{:x}", x.0)
    }
    
}

#[export_name = "\x01print_snake_val"]
extern "sysv64" fn print_snake_val(v: SnakeVal) -> SnakeVal {
    println!("{}", sprint_snake_val(v, Vec::new()));
    return v;
}

/* Implement the following error function. You are free to change the
 * input and output types as needed for your design.
 *
**/
#[export_name = "\x01snake_error"]
extern "sysv64" fn snake_error(rdi: u64, rsi: SnakeVal) {
    /* */
    /* */
    // rdi: code
    // rsi: faulty number/bool
    println!("getting to snake_error with rdi = {}", rdi);
    match rdi {
        0 => eprintln!("arithmetic expected a number: {}", sprint_snake_val(rsi, Vec::new())),
        1 => eprintln!("comparison expected a number: {}", sprint_snake_val(rsi, Vec::new())),
        2 => eprintln!("overflow"),
        3 => eprintln!("if expected a boolean: {}", sprint_snake_val(rsi, Vec::new())),
        4 => eprintln!("logic expected a boolean"),

        5 => eprintln!("called a non-function: {}", sprint_snake_val(rsi, Vec::new())),
        6 => eprintln!("wrong number of arguments"),

        7 => eprintln!("indexed into non-array: {}", sprint_snake_val(rsi, Vec::new())),
        8 => eprintln!("index not a number: {}", sprint_snake_val(rsi, Vec::new())),
        9 => eprintln!("index out of bounds: {}", sprint_snake_val(rsi, Vec::new())),
        
        10 => eprintln!("length
        called with non-array, length called with non-array: {}", sprint_snake_val(rsi, Vec::new())),


        _ => eprintln!("Invalid error code: rsi: {}, rdi: {}", sprint_snake_val(rsi, Vec::new()), rdi),
    }

    std::process::exit(1);
}

/* Implement the following function for checking for equality.
 *
 * For closures you can use simple pointer equality, but for arrays,
 * you should use *structural* equality.
 *
 * */
 /* Optionally, Implement the following function for checking for equality.
 * You may also choose to defined this in assembly code.
 * */

#[export_name = "\x01snake_equals"]
extern "sysv64" fn snake_equals() {
    /* */
    panic!("NYI: snake_equals")
}

fn main() {
    let output = unsafe { start_here() };
    println!("{}", sprint_snake_val(output, Vec::new()));
}
