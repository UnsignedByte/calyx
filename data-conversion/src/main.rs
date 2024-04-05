//use std::env;
use std::fs::read_to_string;
use std::fs::File;
use std::io::{self, Write};
use argh::FromArgs;

fn main() {
    #[derive(FromArgs)]
    /// get arguments to convert
    struct Arguments {

        /// file to convert from 
        #[argh(option)]
        from: String,
    
        /// file to convery to 
        #[argh(option)]
        to: String,
    
        /// type to convert from 
        #[argh(option)]
        ftype: String,
    
        /// type to convert to 
        #[argh(option)]
        totype: String,
    }

    let args: Arguments = argh::from_env();

    let types: Vec<String> = vec!["binary".to_string(), "float".to_string(), "hex".to_string()];
    let mut valid = true;

    if !types.contains(&args.ftype) {
        eprintln!("{} is not a valid type to convert from", args.from);
        valid = false;
    }
    if !types.contains(&args.totype) {
        eprintln!("{} is not a valid type to convert from", args.to);
        valid = false;
    }
    if valid {
        convert(&args.from, &args.to, &args.ftype, &args.totype);
    }
}

/// Converts [filepath_get] from type [convert_from] to type 
/// [convert_to] in [filepath_send]
fn convert(
    filepath_get: &String,
    filepath_send: &String,
    convert_from: &String,
    convert_to: &String,
) {
    // Create a file called converted.txt
    let mut converted = File::create(filepath_send).expect("creation failed");

    if convert_to == "binary" {
        //Convert from hex to binary
        if convert_from == "hex" {
            for line in read_to_string(filepath_get).unwrap().lines() {
                hex_to_binary(line, &mut converted)
                    .expect("Failed to write binary to file");
            }
        //Convert from float to binary
        } else if convert_from == "float" {
            for line in read_to_string(filepath_get).unwrap().lines() {
                float_to_binary(line, &mut converted)
                    .expect("Failed to write binary to file");
            }
        }
    } else if convert_to == "hex" {
        //Convert from binary to hex
        if convert_from == "binary" {
            for line in read_to_string(filepath_get).unwrap().lines() {
                binary_to_hex(line, &mut converted)
                    .expect("Failed to write hex to file");
            }
        }
    } else if convert_to == "float" {
        //Convert from binary to float
        if convert_from == "binary" {
            for line in read_to_string(filepath_get).unwrap().lines() {
                binary_to_float(line, &mut converted)
                    .expect("Failed to write float to file");
            }
        }
    }

    eprintln!(
        "Successfully converted from {} to {} in {}",
        convert_from, convert_to, filepath_send
    );
}

/// Formats [to_format] properly
fn format_binary(to_format: u32) -> String {
    let binary_str = format!("{:032b}", to_format);
    format!(
        "{} {} {}",
        &binary_str[0..1], // Sign bit
        &binary_str[1..9], // Exponent
        &binary_str[9..]   // Significand
    )
}

fn format_hex(to_format: u32) -> String {
    let formatted_hex_str = format!("{:X}", to_format);
    format!("0x{}", &formatted_hex_str)
}

/// Converts [binary_string] to binary and appends to [filepath_send]
fn float_to_binary(
    binary_string: &str,
    filepath_send: &mut File,
) -> std::io::Result<()> {
    let float_of_string: f32;
    // Convert string to float
    match binary_string.parse::<f32>() {
        Ok(parsed_num) => float_of_string = parsed_num,
        Err(_) => {
            panic!("Failed to parse float from string")
        }
    }

    // Convert float to binary
    let binary_of_float = float_of_string.to_bits();
    let formatted_binary_str = format_binary(binary_of_float);

    // Write binary string to the file
    filepath_send.write_all(formatted_binary_str.as_bytes())?;
    filepath_send.write_all(b"\n")?;

    Ok(())
}

/// Converts [hex_string] to binary and appends to [filepath_send]
fn hex_to_binary(hex_string: &str, filepath_send: &mut File) -> io::Result<()> {
    // Convert hex to binary
    let binary_of_hex = match u32::from_str_radix(hex_string, 16) {
        Ok(value) => value,
        Err(err) => {
            return Err(io::Error::new(io::ErrorKind::InvalidData, err))
        }
    };

    // Format nicely
    let formatted_binary_str = format!("{:b}", binary_of_hex);

    // Write binary string to the file
    filepath_send.write_all(formatted_binary_str.as_bytes())?;
    filepath_send.write_all(b"\n")?;

    Ok(())
}

fn binary_to_hex(
    binary_string: &str,
    filepath_send: &mut File,
) -> io::Result<()> {
    let hex_of_binary = match u32::from_str_radix(binary_string, 2) {
        Ok(value) => value,
        Err(err) => {
            return Err(io::Error::new(io::ErrorKind::InvalidData, err))
        }
    };
    
    let formatted_hex_str = format_hex(hex_of_binary);

    filepath_send.write(formatted_hex_str.as_bytes())?;
    filepath_send.write_all(b"\n")?;

    Ok(())
}

fn binary_to_float(
    binary_string: &str,
    filepath_send: &mut File,
) -> io::Result<()> {
    let binary_value = match u32::from_str_radix(binary_string, 2) {
        Ok(value) => value,
        Err(err) => {
            return Err(io::Error::new(io::ErrorKind::InvalidData, err))
        }
    };

    // Interpret the integer as the binary representation of a floating-point number
    let float_value = unsafe { std::mem::transmute::<u32, f32>(binary_value) };

    let formated_float_str = format!("{:?}", float_value);

    filepath_send.write_all(formated_float_str.as_bytes())?;
    filepath_send.write_all(b"\n")?;

    Ok(())
}

// fn fixed_to_binary (
//     fixed_string: &str,
//     filepath_send: &mut File,
//     scale: int,
// ) -> io::Result<()> {

//     }
