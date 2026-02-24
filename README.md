# single-ping

A simple, lightweight ICMP ping library for Rust that supports both IPv4 and IPv6.

## Features

- Support for both IPv4 and IPv6
- Simple API
- Synchronous ping operations
- DNS hostname resolution
- Latency measurement in milliseconds
- Packet validation

## Installation

Add this to your `Cargo.toml`:

```toml
[dependencies]
single-ping = "0.1.1"
```

## Usage

### Basic Example

```rust
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
```

### Ping a Hostname

```rust
use single_ping::ping;

fn main() {
    // Ping google.com with 2 second timeout and 56 bytes of data
    match ping("google.com", 2000, 56) {
        Ok(result) => {
            println!("Latency: {}ms", result.latency_ms);
        }
        Err(e) => eprintln!("Error: {}", e),
    }
}
```

### Check for Dropped Packets

```rust
use single_ping::ping;

fn main() {
    let result = ping("example.com", 1000, 32).unwrap();

    if result.dropped {
        println!("No response received within timeout period");
    } else {
        println!("Response received in {}ms", result.latency_ms);
    }
}
```

## API

### `ping(host: &str, timeout: u64, size: u64) -> Result<PingResult, Box<dyn std::error::Error>>`

Sends an ICMP echo request to the specified host.

**Parameters:**

- `host` - Target host as an IP address or hostname (e.g., "8.8.8.8" or "google.com")
- `timeout` - Maximum time to wait for a response, in milliseconds
- `size` - Size of the data payload in bytes

**Returns:**

- `Ok(PingResult)` - Contains information about the ping result
- `Err(_)` - If the host cannot be resolved or network errors occur

### `PingResult`

The result of a ping operation.

**Fields:**

- `dropped: bool` - Whether the packet was dropped (no response or invalid response)
- `latency_ms: u64` - Round-trip time in milliseconds

## Requirements

### Elevated Privileges

Creating raw ICMP sockets requires elevated privileges:

**Linux/macOS:**

```bash
sudo cargo run
```

Or set capabilities on the binary:

```bash
sudo setcap cap_net_raw+ep target/release/your_binary
```

**Windows:**
Run your terminal or IDE as Administrator.

## Supported Platforms

- Linux
- macOS
- Windows
- Other Unix-like systems

## How It Works

1. **DNS Resolution**: The library first resolves the hostname to an IP address (or parses it if already an IP)
2. **Socket Creation**: Creates a raw ICMP socket (ICMPv4 or ICMPv6 based on the resolved address)
3. **Packet Construction**: Builds an ICMP Echo Request packet with the specified payload size
4. **Send & Receive**: Sends the packet and waits for an Echo Reply within the timeout period
5. **Validation**: Validates the received packet to ensure it's a proper Echo Reply
6. **Latency Calculation**: Measures the round-trip time from send to receive

## Examples

Run the examples with elevated privileges:

```bash
# Basic ping example (if you create one)
sudo cargo run --example basic_ping

# Run tests
sudo cargo test
```

## Dependencies

- [`socket2`](https://crates.io/crates/socket2) - Cross-platform socket operations

## License

Apache-2.0

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## Troubleshooting

### "Permission denied" or "Operation not permitted"

You need to run with elevated privileges (see [Requirements](#requirements)).

### "Host unreachable" or resolution failures

- Check your network connection
- Verify the hostname is correct
- Ensure DNS resolution is working (`ping` command works)

### IPv6 issues

Some networks may not support IPv6. The library will automatically use IPv4 or IPv6 based on the resolved address.

## See Also

- [ICMP Protocol (RFC 792)](https://tools.ietf.org/html/rfc792)
- [ICMPv6 (RFC 4443)](https://tools.ietf.org/html/rfc4443)
