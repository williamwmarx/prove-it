import { TlaError } from "../errors";

// Reads one entry of a zip archive, such as the manifest of a jar, from its central directory.
// Deflated data goes through DecompressionStream, which Node, Bun and browsers all have. Zip64,
// encryption and methods other than stored and deflated are out of scope: tla2tools.jar uses none.

const END_SIGNATURE = 0x06054b50;
const CENTRAL_SIGNATURE = 0x02014b50;
const LOCAL_SIGNATURE = 0x04034b50;
const END_SIZE = 22;
const CENTRAL_HEADER_SIZE = 46;
const LOCAL_HEADER_SIZE = 30;
const MAX_COMMENT_SIZE = 0xffff;
const ENCRYPTED_FLAG = 1;
const STORED = 0;
const DEFLATED = 8;

// The end of central directory record sits last, before a comment of up to 64 KiB.
const findEnd = (view: DataView) => {
  const last = view.byteLength - END_SIZE;
  for (let offset = last; offset >= Math.max(0, last - MAX_COMMENT_SIZE); offset--) {
    if (view.getUint32(offset, true) === END_SIGNATURE) return offset;
  }
  throw new TlaError("Not a zip archive: no end of central directory record.");
};

// slice copies the data out of a Buffer, whose memory Blob doesn't take.
const inflate = async (data: Uint8Array) =>
  new Uint8Array(
    await new Response(
      new Blob([data.slice()]).stream().pipeThrough(new DecompressionStream("deflate-raw")),
    ).arrayBuffer(),
  );

export const readZipEntry = async (
  archive: Uint8Array,
  name: string,
): Promise<Uint8Array | undefined> => {
  const view = new DataView(archive.buffer, archive.byteOffset, archive.byteLength);
  const end = findEnd(view);
  const entryCount = view.getUint16(end + 10, true);
  const decoder = new TextDecoder();
  let offset = view.getUint32(end + 16, true);
  for (let index = 0; index < entryCount; index++) {
    if (view.getUint32(offset, true) !== CENTRAL_SIGNATURE) {
      throw new TlaError("Not a zip archive: a central directory header is missing.");
    }
    const nameLength = view.getUint16(offset + 28, true);
    const nameStart = offset + CENTRAL_HEADER_SIZE;
    if (decoder.decode(archive.subarray(nameStart, nameStart + nameLength)) === name) {
      const flags = view.getUint16(offset + 8, true);
      const method = view.getUint16(offset + 10, true);
      const compressedSize = view.getUint32(offset + 20, true);
      const localOffset = view.getUint32(offset + 42, true);
      if (view.getUint32(localOffset, true) !== LOCAL_SIGNATURE) {
        throw new TlaError(`Not a zip archive: the local header of ${name} is missing.`);
      }
      if (flags & ENCRYPTED_FLAG || (method !== STORED && method !== DEFLATED)) {
        throw new TlaError(
          `Can't read ${name}: it is encrypted or compressed with method ${method}.`,
        );
      }
      const dataStart =
        localOffset +
        LOCAL_HEADER_SIZE +
        view.getUint16(localOffset + 26, true) +
        view.getUint16(localOffset + 28, true);
      const data = archive.subarray(dataStart, dataStart + compressedSize);
      return method === STORED ? data : inflate(data);
    }
    offset +=
      CENTRAL_HEADER_SIZE +
      nameLength +
      view.getUint16(offset + 30, true) +
      view.getUint16(offset + 32, true);
  }
  return undefined;
};
