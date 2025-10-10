//! A simple ICMP ping library for Rust.
//!
//! This library provides a straightforward way to send ICMP echo requests (pings)
//! to hosts using both IPv4 and IPv6. It requires elevated privileges (root/sudo)
//! to create raw sockets.
//!
//! # Examples
//!
//! ```no_run
//! use single_ping::ping;
//!
//! let result = ping("example.com", 1000, 32).unwrap();
//! println!("Ping successful with {}ms latency", result.latency_ms);
//! ```
use socket2::{Domain, Protocol, Socket, Type};
use std::net::{IpAddr, ToSocketAddrs};
use std::time::{Duration, Instant};

/// Result of a ping operation.
///
/// Contains information about whether the ping was successful and the measured latency.
pub struct PingResult {
    /// Whether the packet was dropped (no response received or invalid response)
    pub dropped: bool,
    /// Latency in milliseconds
    pub latency_ms: u64,
}

pub fn ping(host: &str, timeout: u64, size: u64) -> Result<PingResult, Box<dyn std::error::Error>> {
    // Convert timeout from milliseconds to Duration
    let timeout_duration = Duration::from_millis(timeout);

    // Resolve the host to an IP address
    let ip = resolve_host(host)?;

    // Create raw ICMP socket based on IP version
    let (socket, _domain, _protocol) = match ip {
        IpAddr::V4(_) => {
            let socket = Socket::new_raw(Domain::IPV4, Type::RAW, Some(Protocol::ICMPV4))
                .unwrap_or_else(|_| {
                    println!("Failed to create IPv4 socket. You may need to run with `sudo`.");
                    std::process::exit(1);
                });
            (socket, Domain::IPV4, Protocol::ICMPV4)
        }
        IpAddr::V6(_) => {
            let socket = Socket::new_raw(Domain::IPV6, Type::RAW, Some(Protocol::ICMPV6))?;
            (socket, Domain::IPV6, Protocol::ICMPV6)
        }
    };

    socket.set_read_timeout(Some(timeout_duration)).unwrap();

    // Build ICMP packet based on IP version
    let packet = match ip {
        IpAddr::V4(_) => build_icmpv4_packet(size),
        IpAddr::V6(_) => build_icmpv6_packet(size),
    };

    // Send packet
    let start_time = Instant::now();
    let addr = std::net::SocketAddr::new(ip, 0);
    socket.send_to(&packet, &addr.into()).unwrap();

    // Receive reply
    let mut buffer = [std::mem::MaybeUninit::<u8>::uninit(); 1024];
    match socket.recv_from(&mut buffer) {
        Ok((bytes_received, _)) => {
            let end_time = Instant::now();
            let latency = end_time.duration_since(start_time).as_millis() as u64;

            // Validate reply based on IP version
            let is_valid = match ip {
                IpAddr::V4(_) => validate_icmpv4_reply(&buffer, bytes_received),
                IpAddr::V6(_) => validate_icmpv6_reply(&buffer, bytes_received),
            };

            Ok(PingResult {
                dropped: !is_valid,
                latency_ms: latency,
            })
        }
        Err(_) => {
            // Timeout or other error
            let end_time = Instant::now();
            let latency = end_time.duration_since(start_time).as_millis() as u64;
            Ok(PingResult {
                dropped: true,
                latency_ms: latency,
            })
        }
    }
}

/// Calculates the ICMP checksum for a packet.
///
/// The checksum is calculated as the one's complement of the one's complement sum
/// of all 16-bit words in the packet. This is the standard Internet checksum algorithm
/// used for ICMP packets.
///
/// # Arguments
///
/// * `packet` - The packet data for which to calculate the checksum
///
/// # Returns
///
/// The calculated checksum as a 16-bit unsigned integer
fn calculate_icmp_checksum(packet: &[u8]) -> u16 {
    let mut sum: u32 = 0;

    // Sum all 16-bit words
    for chunk in packet.chunks(2) {
        let word = if chunk.len() == 2 {
            u16::from_be_bytes([chunk[0], chunk[1]])
        } else {
            u16::from_be_bytes([chunk[0], 0])
        };
        sum += word as u32;
    }

    // Add carry bits
    while (sum >> 16) != 0 {
        sum = (sum & 0xFFFF) + (sum >> 16);
    }

    // One's complement
    !sum as u16
}

/// Resolves a hostname or IP address string to an `IpAddr`.
///
/// This function first attempts to parse the input as a direct IP address.
/// If that fails, it performs DNS resolution to convert a hostname to an IP address.
///
/// # Arguments
///
/// * `host` - A string containing either an IP address (e.g., "8.8.8.8") or hostname (e.g., "google.com")
///
/// # Returns
///
/// * `Ok(IpAddr)` - The resolved IP address
/// * `Err(std::io::Error)` - If the host cannot be parsed or resolved
fn resolve_host(host: &str) -> Result<IpAddr, std::io::Error> {
    // First try to parse as IP address directly
    if let Ok(ip) = host.parse::<IpAddr>() {
        return Ok(ip);
    }

    // Try DNS resolution
    let address = format!("{}:80", host); // Add dummy port for resolution
    match address.to_socket_addrs() {
        Ok(mut addrs) => {
            if let Some(addr) = addrs.next() {
                Ok(addr.ip())
            } else {
                Err(std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    format!("No addresses found for host: {}", host),
                ))
            }
        }
        Err(e) => {
            Err(std::io::Error::new(
                std::io::ErrorKind::HostUnreachable,
                format!("Failed to resolve host {}: {}", host, e),
            ))
        }
    }
}

/// Builds an ICMPv4 Echo Request packet.
///
/// Constructs a complete ICMP packet with the standard 8-byte header followed by
/// data payload. The packet includes:
/// - Type field set to 8 (Echo Request)
/// - Code field set to 0
/// - A calculated checksum
/// - Identifier and sequence number fields
/// - Data payload filled with a repeating pattern
///
/// # Arguments
///
/// * `size` - The size of the data payload in bytes (excluding the 8-byte header)
///
/// # Returns
///
/// A vector containing the complete ICMP packet with calculated checksum
fn build_icmpv4_packet(size: u64) -> Vec<u8> {
    // Build ICMP Echo Request packet
    // ICMP header (8 bytes) + size padding
    let mut packet = vec![0u8; 8 + size as usize];

    // ICMP Header
    packet[0] = 8; // Type: Echo Request
    packet[1] = 0; // Code: 0
    packet[2] = 0; // Checksum (will be calculated)
    packet[3] = 0; // Checksum
    packet[4] = 0; // Identifier (can be process ID)
    packet[5] = 1; // Identifier
    packet[6] = 0; // Sequence number
    packet[7] = 1; // Sequence number

    // Fill data portion with pattern
    for i in 8..packet.len() {
        packet[i] = (i % 256) as u8;
    }

    // Calculate checksum
    let checksum = calculate_icmp_checksum(&packet);
    packet[2] = (checksum >> 8) as u8;
    packet[3] = (checksum & 0xff) as u8;

    packet
}

/// Builds an ICMPv6 Echo Request packet.
///
/// Constructs a complete ICMPv6 packet with the standard 8-byte header followed by
/// data payload. The packet includes:
/// - Type field set to 128 (Echo Request for ICMPv6)
/// - Code field set to 0
/// - Checksum fields set to 0 (calculated by the kernel for IPv6)
/// - Identifier and sequence number fields
/// - Data payload filled with a repeating pattern
///
/// # Arguments
///
/// * `size` - The size of the data payload in bytes (excluding the 8-byte header)
///
/// # Returns
///
/// A vector containing the complete ICMPv6 packet (checksum will be calculated by kernel)
fn build_icmpv6_packet(size: u64) -> Vec<u8> {
    // Build ICMPv6 Echo Request packet
    // ICMPv6 header (8 bytes) + size padding
    let mut packet = vec![0u8; 8 + size as usize];

    // ICMPv6 Header
    packet[0] = 128; // Type: Echo Request (ICMPv6)
    packet[1] = 0; // Code: 0
    packet[2] = 0; // Checksum (calculated by kernel for IPv6)
    packet[3] = 0; // Checksum
    packet[4] = 0; // Identifier
    packet[5] = 1; // Identifier
    packet[6] = 0; // Sequence number
    packet[7] = 1; // Sequence number

    // Fill data portion with pattern
    for i in 8..packet.len() {
        packet[i] = (i % 256) as u8;
    }

    packet
}

/// Validates an ICMPv4 Echo Reply packet.
///
/// Checks if the received packet is a valid ICMP Echo Reply by examining the ICMP type field.
/// The function accounts for the IPv4 header (20 bytes) before the ICMP data.
///
/// # Arguments
///
/// * `buffer` - The raw packet buffer containing the IPv4 header and ICMP data
/// * `bytes_received` - The number of bytes received in the buffer
///
/// # Returns
///
/// `true` if the packet is a valid Echo Reply (type 0), `false` otherwise
fn validate_icmpv4_reply(buffer: &[std::mem::MaybeUninit<u8>], bytes_received: usize) -> bool {
    // Basic validation - check if it's an ICMP Echo Reply
    if bytes_received >= 28 {
        // IP header (20) + ICMP header (8)
        let icmp_type = unsafe { buffer[20].assume_init() }; // ICMP type is at offset 20 (after IP header)
        icmp_type == 0// Echo Reply
    } else {
        false
    }
}

/// Validates an ICMPv6 Echo Reply packet.
///
/// Checks if the received packet is a valid ICMPv6 Echo Reply by examining the ICMP type field.
/// Unlike IPv4, ICMPv6 packets do not have an IP header in the received data.
///
/// # Arguments
///
/// * `buffer` - The raw packet buffer containing the ICMPv6 data
/// * `bytes_received` - The number of bytes received in the buffer
///
/// # Returns
///
/// `true` if the packet is a valid Echo Reply (type 129), `false` otherwise
fn validate_icmpv6_reply(buffer: &[std::mem::MaybeUninit<u8>], bytes_received: usize) -> bool {
    // For ICMPv6, no IP header to skip, ICMP header starts immediately
    if bytes_received >= 8 {
        let icmp_type = unsafe { buffer[0].assume_init() };
        icmp_type == 129// ICMPv6 Echo Reply
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{Ipv4Addr, Ipv6Addr};

    #[test]
    fn test_resolve_host_ipv4() {
        let result = resolve_host("127.0.0.1");
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)));
    }

    #[test]
    fn test_resolve_host_ipv6() {
        let result = resolve_host("::1");
        assert!(result.is_ok());
        assert_eq!(
            result.unwrap(),
            IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1))
        );
    }

    #[test]
    fn test_resolve_host_localhost() {
        let result = resolve_host("localhost");
        assert!(result.is_ok());
        // localhost should resolve to either 127.0.0.1 or ::1
        let ip = result.unwrap();
        assert!(
            ip == IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1))
                || ip == IpAddr::V6(Ipv6Addr::new(0, 0, 0, 0, 0, 0, 0, 1))
        );
    }

    #[test]
    fn test_resolve_host_invalid() {
        let result = resolve_host("invalid.domain.that.does.not.exist.12345");
        assert!(result.is_err());
    }

    #[test]
    fn test_build_icmpv4_packet() {
        let packet = build_icmpv4_packet(8);

        // Should be 8 (header) + 8 (size) = 16 bytes
        assert_eq!(packet.len(), 16);

        // Check ICMP header fields
        assert_eq!(packet[0], 8); // Type: Echo Request
        assert_eq!(packet[1], 0); // Code: 0
        assert_eq!(packet[4], 0); // Identifier high byte
        assert_eq!(packet[5], 1); // Identifier low byte
        assert_eq!(packet[6], 0); // Sequence high byte
        assert_eq!(packet[7], 1); // Sequence low byte

        // Check data pattern
        for i in 8..packet.len() {
            assert_eq!(packet[i], (i % 256) as u8);
        }

        // Checksum should be calculated (non-zero)
        assert!(packet[2] != 0 || packet[3] != 0);
    }

    #[test]
    fn test_build_icmpv6_packet() {
        let packet = build_icmpv6_packet(8);

        // Should be 8 (header) + 8 (size) = 16 bytes
        assert_eq!(packet.len(), 16);

        // Check ICMPv6 header fields
        assert_eq!(packet[0], 128); // Type: Echo Request (ICMPv6)
        assert_eq!(packet[1], 0); // Code: 0
        assert_eq!(packet[2], 0); // Checksum (calculated by kernel)
        assert_eq!(packet[3], 0); // Checksum
        assert_eq!(packet[4], 0); // Identifier high byte
        assert_eq!(packet[5], 1); // Identifier low byte
        assert_eq!(packet[6], 0); // Sequence high byte
        assert_eq!(packet[7], 1); // Sequence low byte

        // Check data pattern
        for i in 8..packet.len() {
            assert_eq!(packet[i], (i % 256) as u8);
        }
    }

    #[test]
    fn test_validate_icmpv4_reply_valid() {
        // Create a mock IPv4 ICMP Echo Reply packet
        let mut buffer = [std::mem::MaybeUninit::<u8>::uninit(); 1024];

        // Fill IP header (20 bytes) + ICMP header (8 bytes)
        for i in 0..28 {
            buffer[i] = std::mem::MaybeUninit::new(0);
        }
        // Set ICMP type to Echo Reply (0) at offset 20
        buffer[20] = std::mem::MaybeUninit::new(0);

        assert!(validate_icmpv4_reply(&buffer, 28));
    }

    #[test]
    fn test_validate_icmpv4_reply_invalid_type() {
        let mut buffer = [std::mem::MaybeUninit::<u8>::uninit(); 1024];

        // Fill IP header (20 bytes) + ICMP header (8 bytes)
        for i in 0..28 {
            buffer[i] = std::mem::MaybeUninit::new(0);
        }
        // Set ICMP type to something other than Echo Reply
        buffer[20] = std::mem::MaybeUninit::new(8); // Echo Request instead of Reply

        assert!(!validate_icmpv4_reply(&buffer, 28));
    }

    #[test]
    fn test_validate_icmpv4_reply_too_short() {
        let buffer = [std::mem::MaybeUninit::<u8>::uninit(); 1024];

        // Packet too short (less than 28 bytes)
        assert!(!validate_icmpv4_reply(&buffer, 20));
    }

    #[test]
    fn test_validate_icmpv6_reply_valid() {
        let mut buffer = [std::mem::MaybeUninit::<u8>::uninit(); 1024];

        // Set ICMPv6 type to Echo Reply (129) at offset 0
        buffer[0] = std::mem::MaybeUninit::new(129);
        for i in 1..8 {
            buffer[i] = std::mem::MaybeUninit::new(0);
        }

        assert!(validate_icmpv6_reply(&buffer, 8));
    }

    #[test]
    fn test_validate_icmpv6_reply_invalid_type() {
        let mut buffer = [std::mem::MaybeUninit::<u8>::uninit(); 1024];

        // Set ICMPv6 type to something other than Echo Reply
        buffer[0] = std::mem::MaybeUninit::new(128); // Echo Request instead of Reply
        for i in 1..8 {
            buffer[i] = std::mem::MaybeUninit::new(0);
        }

        assert!(!validate_icmpv6_reply(&buffer, 8));
    }

    #[test]
    fn test_validate_icmpv6_reply_too_short() {
        let buffer = [std::mem::MaybeUninit::<u8>::uninit(); 1024];

        // Packet too short (less than 8 bytes)
        assert!(!validate_icmpv6_reply(&buffer, 4));
    }

    #[test]
    fn test_calculate_icmp_checksum() {
        // Test with a simple packet
        let mut packet = vec![8, 0, 0, 0, 0, 1, 0, 1]; // Basic ICMP header

        // Clear checksum field
        packet[2] = 0;
        packet[3] = 0;

        let checksum = calculate_icmp_checksum(&packet);

        // Checksum should be non-zero for this packet
        assert_ne!(checksum, 0);

        // Verify checksum by including it in the packet and recalculating
        packet[2] = (checksum >> 8) as u8;
        packet[3] = (checksum & 0xff) as u8;

        let verify_checksum = calculate_icmp_checksum(&packet);
        assert_eq!(verify_checksum, 0); // Should be 0 when checksum is correct
    }
}
