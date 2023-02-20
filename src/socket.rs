use std::{
    io::{Read, Write},
    net::TcpStream,
};

use crate::{exception::Exception, exprs::Expr, interpreter::MethodType, structs::StructInterface};

struct Socket {
    stream: Option<TcpStream>,
}

impl Socket {
    fn new() -> Self {
        Self { stream: None }
    }

    fn connect(&mut self, host: &str, port: u16) -> Result<(), String> {
        match TcpStream::connect(format!("{}:{}", host, port)) {
            Ok(stream) => {
                self.stream = Some(stream);
                Ok(())
            }
            Err(e) => Err(e.to_string()),
        }
    }

    fn send(&mut self, data: &[u8]) -> Result<(), String> {
        match &mut self.stream {
            Some(stream) => match stream.write(data) {
                Ok(_) => Ok(()),
                Err(e) => Err(e.to_string()),
            },
            None => Err("Not connected".to_owned()),
        }
    }

    fn recv(&mut self, size: usize) -> Result<Vec<u8>, String> {
        match &mut self.stream {
            Some(stream) => {
                let mut buffer = vec![0; size];
                match stream.read(&mut buffer) {
                    Ok(read) => Ok(buffer[..read].to_vec()),
                    Err(e) => Err(e.to_string()),
                }
            }
            None => Err("Not connected".to_owned()),
        }
    }

    fn close(&mut self) -> Result<(), String> {
        match &mut self.stream {
            Some(stream) => match stream.shutdown(std::net::Shutdown::Both) {
                Ok(_) => {
                    self.stream = None;
                    Ok(())
                }
                Err(e) => Err(e.to_string()),
            },
            None => Err("Not connected".to_owned()),
        }
    }

    fn __str__(&mut self) -> Result<Expr, Exception> {
        Ok(Expr::Str(format!("Socket({:?})", self.stream)))
    }
}

impl StructInterface for Socket {
    fn get(&self, name: &str) -> Option<Expr> {
        None
    }

    fn set(&mut self, name: &str, value: Expr) {}

    fn get_method(&self, name: &str) -> Option<crate::interpreter::MethodType> {
        match name {
            "__str__" => Some(MethodType::Native(|this, _args| {
                let this = this.downcast_mut::<Self>().unwrap();
                this.__str__()
            })),
            "connect" => Some(MethodType::Native(|this, args| {
                let this = this.downcast_mut::<Self>().unwrap();
                let host = match args.get(0) {
                    Some(Expr::Str(host)) => host,
                    _ => return Err(Exception::new("Expected string for host")),
                };
                let port = match args.get(1) {
                    Some(Expr::Number(port)) => *port as u16,
                    _ => return Err(Exception::new("Expected number for port")),
                };
                match this.connect(host, port) {
                    Ok(_) => Ok(Expr::Null),
                    Err(e) => Err(Exception::new(e)),
                }
            })),
            "send" => Some(MethodType::Native(|this, args| {
                let this = this.downcast_mut::<Self>().unwrap();
                let data = match args.get(0) {
                    Some(Expr::Str(data)) => data.as_bytes(),
                    _ => return Err(Exception::new("Expected string for data")),
                };
                match this.send(data) {
                    Ok(_) => Ok(Expr::Null),
                    Err(e) => Err(Exception::new(e)),
                }
            })),
            "recv" => Some(MethodType::Native(|this, args| {
                let this = this.downcast_mut::<Self>().unwrap();
                let size = match args.get(0) {
                    Some(Expr::Number(size)) => *size as usize,
                    _ => return Err(Exception::new("Expected number for size")),
                };
                match this.recv(size) {
                    Ok(data) => Ok(Expr::Str(String::from_utf8(data).unwrap())),
                    Err(e) => Err(Exception::new(e)),
                }
            })),
            _ => None,
        }
    }
}

#[derive(Clone)]
pub struct SocketBuilder {}
impl crate::structs::StructBuilder for SocketBuilder {
    fn construct(&self, _args: Vec<(String, Expr)>) -> Result<Box<dyn StructInterface>, Exception> {
        Ok(Box::new(Socket::new()))
    }
}
