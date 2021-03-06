pub fn to_hex_string(bytes: &Vec<u8>) -> String {
    return bytes.iter()
        .map(|b| format!("{:02x}", b))
        .collect::<Vec<_>>()
        .join("");
}
