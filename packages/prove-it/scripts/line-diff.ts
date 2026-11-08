// The lines one text drops ("-line") and the other adds ("+line"), in order, by Myers' shortest
// edit script after the common start and end. Past MAXIMUM_EDITS edits it gives up on the middle
// and reports all of it as changed, which still names every differing line.

const MAXIMUM_EDITS = 2000;

const getMiddleDiff = (left: string[], right: string[]): string[] => {
  const size = left.length + right.length;
  const limit = Math.min(size, MAXIMUM_EDITS);
  const offset = limit + 1;
  const furthest = new Int32Array(2 * offset + 1);
  const history: Int32Array[] = [];
  for (let edits = 0; edits <= limit; edits++) {
    history.push(furthest.slice());
    for (let diagonal = -edits; diagonal <= edits; diagonal += 2) {
      const isDown =
        diagonal === -edits ||
        (diagonal !== edits && furthest[offset + diagonal - 1] < furthest[offset + diagonal + 1]);
      const start = isDown ? furthest[offset + diagonal + 1] : furthest[offset + diagonal - 1] + 1;
      const end = { x: start };
      while (
        end.x < left.length &&
        end.x - diagonal < right.length &&
        left[end.x] === right[end.x - diagonal]
      ) {
        end.x++;
      }
      furthest[offset + diagonal] = end.x;
      if (end.x >= left.length && end.x - diagonal >= right.length) {
        return getEditScript(left, right, history, offset, edits, diagonal);
      }
    }
  }
  return [...left.map((line) => `-${line}`), ...right.map((line) => `+${line}`)];
};

// Walks the snakes back from the end, from the furthest point of each round before it.
const getEditScript = (
  left: string[],
  right: string[],
  history: Int32Array[],
  offset: number,
  edits: number,
  diagonal: number,
) => {
  const script: string[] = [];
  const position = { x: left.length, y: right.length, diagonal };
  for (let round = edits; round > 0; round--) {
    const before = history[round];
    const isDown =
      position.diagonal === -round ||
      (position.diagonal !== round &&
        before[offset + position.diagonal - 1] < before[offset + position.diagonal + 1]);
    const previous = isDown ? position.diagonal + 1 : position.diagonal - 1;
    const previousX = before[offset + previous];
    const startX = isDown ? previousX : previousX + 1;
    // The snake: equal lines from (startX, startX - diagonal) to the position.
    position.x = startX;
    position.y = startX - position.diagonal;
    script.push(isDown ? `+${right[position.y - 1]}` : `-${left[position.x - 1]}`);
    position.x = previousX;
    position.y = previousX - previous;
    position.diagonal = previous;
  }
  return script.reverse();
};

export const getLineDiff = (left: string[], right: string[]): string[] => {
  const start = { index: 0 };
  while (
    start.index < left.length &&
    start.index < right.length &&
    left[start.index] === right[start.index]
  ) {
    start.index++;
  }
  const end = { length: 0 };
  while (
    end.length < left.length - start.index &&
    end.length < right.length - start.index &&
    left[left.length - 1 - end.length] === right[right.length - 1 - end.length]
  ) {
    end.length++;
  }
  return getMiddleDiff(
    left.slice(start.index, left.length - end.length),
    right.slice(start.index, right.length - end.length),
  );
};
