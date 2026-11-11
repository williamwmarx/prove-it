//! One entry of a zip archive, such as the manifest of a jar, read from its central directory as
//! `readZipEntry` in `src/tlc/zip.ts` reads it. What it can't read with certainty, it declines:
//! zip64, encryption, methods other than stored and deflated, and data whose CRC-32 doesn't match.

use crate::inflate::inflate;

const END_SIGNATURE: u32 = 0x0605_4b50;
const ZIP64_LOCATOR_SIGNATURE: u32 = 0x0706_4b50;
const CENTRAL_SIGNATURE: u32 = 0x0201_4b50;
const LOCAL_SIGNATURE: u32 = 0x0403_4b50;
const END_SIZE: usize = 22;
const ZIP64_LOCATOR_SIZE: usize = 20;
const CENTRAL_HEADER_SIZE: usize = 46;
const LOCAL_HEADER_SIZE: usize = 30;
const MAX_COMMENT_SIZE: usize = 0xffff;
/// General purpose flags 0 and 6: the entry is encrypted, traditionally or strongly.
const ENCRYPTED_FLAGS: u16 = 1 | 1 << 6;
const STORED: u16 = 0;
const DEFLATED: u16 = 8;

/// The archive's bytes, read little-endian at an offset, where a read past the end is an error.
struct Archive<'a>(&'a [u8]);

impl Archive<'_> {
    fn get(&self, offset: usize, length: usize) -> Result<&[u8], String> {
        self.0
            .get(offset..offset.saturating_add(length))
            .ok_or_else(|| "a zip archive that ends early".into())
    }

    fn u16(&self, offset: usize) -> Result<u16, String> {
        let bytes = self.get(offset, 2)?;
        Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
    }

    fn u32(&self, offset: usize) -> Result<u32, String> {
        let bytes = self.get(offset, 4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }
}

/// The entry named `name` of the archive, None where it has none, or why it can't be read.
pub fn read_entry(archive: &[u8], name: &str) -> Result<Option<Vec<u8>>, String> {
    let archive = Archive(archive);
    // The end of central directory record sits last, before a comment of up to 64 KiB.
    let last = archive
        .0
        .len()
        .checked_sub(END_SIZE)
        .ok_or("no end of central directory record")?;
    let end = (last.saturating_sub(MAX_COMMENT_SIZE)..=last)
        .rev()
        .find(|&offset| archive.u32(offset) == Ok(END_SIGNATURE))
        .ok_or("no end of central directory record")?;
    let is_zip64 = end >= ZIP64_LOCATOR_SIZE
        && archive.u32(end - ZIP64_LOCATOR_SIZE)? == ZIP64_LOCATOR_SIGNATURE;
    let entry_count = archive.u16(end + 10)?;
    let directory_offset = archive.u32(end + 16)?;
    if is_zip64 || entry_count == u16::MAX || directory_offset == u32::MAX {
        return Err("a zip64 archive".into());
    }
    if archive.u16(end + 4)? != 0 || archive.u16(end + 6)? != 0 {
        return Err("an archive split across disks".into());
    }
    let mut offset = directory_offset as usize;
    for _ in 0..entry_count {
        if archive.u32(offset)? != CENTRAL_SIGNATURE {
            return Err("a central directory header is missing".into());
        }
        let name_length = usize::from(archive.u16(offset + 28)?);
        let extra_length = usize::from(archive.u16(offset + 30)?);
        let comment_length = usize::from(archive.u16(offset + 32)?);
        if archive.get(offset + CENTRAL_HEADER_SIZE, name_length)? == name.as_bytes() {
            return read_data(&archive, offset, name).map(Some);
        }
        offset += CENTRAL_HEADER_SIZE + name_length + extra_length + comment_length;
    }
    Ok(None)
}

/// The data of the entry whose central directory header is at `header`.
fn read_data(archive: &Archive, header: usize, name: &str) -> Result<Vec<u8>, String> {
    let flags = archive.u16(header + 8)?;
    let method = archive.u16(header + 10)?;
    let crc = archive.u32(header + 16)?;
    let compressed_size = archive.u32(header + 20)?;
    let size = archive.u32(header + 24)?;
    let local = archive.u32(header + 42)?;
    if [compressed_size, size, local].contains(&u32::MAX) {
        return Err(format!("{name}, a zip64 entry"));
    }
    if flags & ENCRYPTED_FLAGS != 0 {
        return Err(format!("{name}, an encrypted entry"));
    }
    let local = local as usize;
    if archive.u32(local)? != LOCAL_SIGNATURE {
        return Err(format!("{name}, whose local header is missing"));
    }
    let start = local
        + LOCAL_HEADER_SIZE
        + usize::from(archive.u16(local + 26)?)
        + usize::from(archive.u16(local + 28)?);
    let compressed = archive.get(start, compressed_size as usize)?;
    let data = match method {
        STORED => compressed.to_vec(),
        DEFLATED => {
            inflate(compressed, size as usize).map_err(|reason| format!("{name}: {reason}"))?
        }
        _ => return Err(format!("{name}, compressed with method {method}")),
    };
    if data.len() != size as usize {
        return Err(format!("{name}, whose size doesn't match its entry's"));
    }
    if get_crc(&data) != crc {
        return Err(format!("{name}, whose CRC-32 doesn't match its entry's"));
    }
    Ok(data)
}

/// The CRC-32 a zip archive checks its entries' data with.
fn get_crc(data: &[u8]) -> u32 {
    !data.iter().fold(!0u32, |crc, &byte| {
        (0..8).fold(crc ^ u32::from(byte), |crc, _| {
            (crc >> 1) ^ (0xedb8_8320 & (crc & 1).wrapping_neg())
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Jars as Python's zipfile writes them: the manifest deflated (in a dynamic Huffman block),
    /// and in the 1.7.4 jar stored.
    const MASTER_JAR: &[u8] = include_bytes!("../fixtures/tla2tools.jar");
    const JAR_174: &[u8] = include_bytes!("../fixtures/tla2tools-1.7.4.jar");
    const MANIFEST: &str = "META-INF/MANIFEST.MF";

    fn get_manifest(tag: &str, branch: &str) -> Vec<u8> {
        format!(
            "Manifest-Version: 1.0\r\nAnt-Version: Apache Ant 1.10.14\r\nCreated-By: 11.0.25+9-LTS (Eclipse Adoptium)\r\nImplementation-Title: TLA+ Tools\r\nImplementation-Version: 1.8.0 10 November 2026\r\nImplementation-Vendor: Microsoft Corp.\r\nMain-class: tlc2.TLC\r\nClass-Path: CommunityModules-deps.jar CommunityModules.jar\r\nX-Git-Branch: {branch}\r\nX-Git-Tag: {tag}\r\nX-Git-Revision: d8fb231d1c0e4b6a0e1b0bb2f3a1c4f5e6a7b8c9\r\nX-Git-ShortRevision: d8fb231\r\nX-Git-BuildNumber: {branch}_{tag}_d8fb231\r\nX-Git-Commits-Count: 7000\r\nApplication-Name: TLC\r\nPermissions: all-permissions\r\n\r\n"
        )
        .into_bytes()
    }

    // Where the central directory header of the manifest starts: its name is the last in the jar.
    fn find_manifest_header(archive: &[u8]) -> usize {
        archive
            .windows(MANIFEST.len())
            .rposition(|window| window == MANIFEST.as_bytes())
            .expect("a manifest")
            - CENTRAL_HEADER_SIZE
    }

    #[test]
    fn reads_a_deflated_and_a_stored_manifest() {
        assert_eq!(
            read_entry(MASTER_JAR, MANIFEST),
            Ok(Some(get_manifest("v1.8.0", "master")))
        );
        assert_eq!(
            read_entry(JAR_174, MANIFEST),
            Ok(Some(get_manifest("v1.7.4", "HEAD")))
        );
        assert_eq!(read_entry(JAR_174, "META-INF/"), Ok(Some(Vec::new())));
        assert_eq!(read_entry(MASTER_JAR, "META-INF/INDEX.LIST"), Ok(None));
    }

    #[test]
    fn declines_what_it_cant_read_with_certainty() {
        let header = find_manifest_header(MASTER_JAR);
        let read_changed = |archive: &[u8], at: usize, bytes: &[u8]| {
            let mut changed = archive.to_vec();
            changed[at..at + bytes.len()].copy_from_slice(bytes);
            read_entry(&changed, MANIFEST)
        };
        // Method 12 is bzip2.
        assert_eq!(
            read_changed(MASTER_JAR, header + 10, &[12]),
            Err("META-INF/MANIFEST.MF, compressed with method 12".into())
        );
        assert_eq!(
            read_changed(MASTER_JAR, header + 8, &[1]),
            Err("META-INF/MANIFEST.MF, an encrypted entry".into())
        );
        assert_eq!(
            read_changed(MASTER_JAR, header + 20, &[0xff; 4]),
            Err("META-INF/MANIFEST.MF, a zip64 entry".into())
        );
        assert_eq!(
            read_changed(MASTER_JAR, MASTER_JAR.len() - END_SIZE + 16, &[0xff; 4]),
            Err("a zip64 archive".into())
        );
        let tag = JAR_174
            .windows(6)
            .position(|window| window == b"v1.7.4")
            .expect("the tag");
        assert_eq!(
            read_changed(JAR_174, tag, b"v1.7.5"),
            Err("META-INF/MANIFEST.MF, whose CRC-32 doesn't match its entry's".into())
        );
        assert_eq!(
            read_entry(b"not a zip archive at all", MANIFEST),
            Err("no end of central directory record".into())
        );
        assert_eq!(
            read_entry(&MASTER_JAR[..MASTER_JAR.len() / 2], MANIFEST),
            Err("no end of central directory record".into())
        );
    }
}
