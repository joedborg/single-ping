use single_ping::ping;

fn main() {
    // Ping with 1000ms timeout and 32 bytes of data
    match ping("8.8.8.8", 1000, 32) {
        Ok(result) => {
            if result.dropped {
                println!("Packet dropped!");
            } else {
                println!("Ping successful! Latency: {}ms", result.latency_ms);
            }
        }
        Err(e) => eprintln!("Ping failed: {}", e),
    }
}
