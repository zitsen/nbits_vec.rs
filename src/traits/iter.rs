use ::NbitsVec;
use num::PrimInt;
use typenum::NonZero;
use typenum::uint::Unsigned;

pub struct Iter<'a, N:'a, Block: 'a> where N: Unsigned + NonZero, Block: PrimInt {
    vec: &'a NbitsVec<N, Block>,
    pos: usize,
}

impl<'a, N:'a, Block: 'a> Iter<'a, N, Block> where N: Unsigned + NonZero, Block: PrimInt {
}

impl<'a, N:'a, Block: 'a> Iterator for Iter<'a, N, Block> where N: Unsigned + NonZero, Block: PrimInt {
    type Item = Block;

    #[inline]
    fn next(&mut self) -> Option<Block> {
        self.pos += 1;
        if self.vec.len() > self.pos {
            Some(self.vec.get(self.pos))
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.vec.len() {
            len if len > self.pos => {
                let diff = len - self.pos;
                (diff, Some(diff))
            },
            _ => (0, None),
        }
    }

    #[inline]
    fn count(self) -> usize {
        self.size_hint().0
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Block> {
        self.pos += n;
        if self.vec.len() > self.pos {
            Some(self.vec.get(self.pos))
        } else {
            None
        }
    }
}

impl<'a, N:'a, Block: 'a> IntoIterator for &'a NbitsVec<N, Block> where N: Unsigned + NonZero, Block: PrimInt {
    type Item = Block;
    type IntoIter = Iter<'a, N, Block>;

    fn into_iter(self) -> Iter<'a, N, Block> {
        Iter {
            vec: self,
            pos: 0,
        }
    }
}


#[cfg(test)]
mod tests {
    use ::{NbitsVec, N2};
    type NV = NbitsVec<N2, usize>;

    #[test]
    fn into_iter() {
        let vec = NV::new();
        for val in vec.into_iter() {
            let _ = val;
        }

    }
}
