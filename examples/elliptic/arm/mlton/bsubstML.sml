structure bsubstML :> bsubstML =
struct
  nonfix MEM_WRITE MEM_WRITE_WORD MEM_WRITE_HALF MEM_WRITE_BYTE SET_HALF
         SET_BYTE FORMAT GET_BYTE GET_HALF ADDR30 mem_items empty_memory
         mem_write_block mem_write mem_read |: data_size Word Half
         Byte formats_size UnsignedWord UnsignedHalfWord SignedHalfWord
         UnsignedByte SignedByte * / div mod + - ^ @ <> > < >= <= := o
         before;
  
  open numML fcpML wordsML;
  type mem = (word30, word32) Redblackmap.dict
  val mem_updates = ref ([]: word30 list)
  datatype formats
       = SignedByte
       | UnsignedByte
       | SignedHalfWord
       | UnsignedHalfWord
       | UnsignedWord
  fun formats_size x = ZERO
    
  datatype data = Byte of word8 | Half of word16 | Word of word32
  fun data_size (Byte(a)) = ONE
    | data_size (Half(a)) = ONE
    | data_size (Word(a)) = ONE
    
  fun |: a l =
        fn m => fn b =>
        if word_ls a b andalso < (- (w2n b) (w2n a)) (listML.LENGTH l)
          then listML.EL (- (w2n b) (w2n a)) l else m b
    
  fun fromNum32 n =
        wordsML.fromNum(numML.fromHexString n, fcpML.ITSELF(numML.fromInt 32))

  fun mem_read (m,a) = Redblackmap.find(m:mem, a)
                       handle NotFound => fromNum32 "E6000010"

  fun mem_write m a d = (:= (mem_updates, a :: !mem_updates);
                         Redblackmap.insert(m:mem, a, d))

  fun mem_write_block m a [] = m
    | mem_write_block m a (d::l) =
        mem_write_block (mem_write m a d)
          (word_add a (n2w_itself (ONE,fcpML.ITSELF(numML.fromInt 30)))) l

  fun word_compare(v, w) =
    let val m = w2n v and n = w2n w in
      if m = n then
        EQUAL
      else
        if < m n then LESS else GREATER
    end

  val empty_memory = (Redblackmap.mkDict word_compare):mem

  fun mem_items m = Redblackmap.listItems m
    
  fun ADDR30 addr =
        word_extract_itself (fcpML.ITSELF (numML.fromDecString"30"))
          (fromString"31") TWO addr
    
  fun GET_HALF oareg data =
        if index oareg ONE
          then word_extract_itself
                 (fcpML.ITSELF (numML.fromDecString"16"))
                 (fromString"31") (fromString"16") data
          else word_extract_itself
                 (fcpML.ITSELF (numML.fromDecString"16"))
                 (fromString"15") ZERO data
    
  fun GET_BYTE oareg data =
        case
          word_eq oareg
            (n2w_itself (ZERO,(fcpML.ITSELF (numML.fromDecString"2"))))
         of true =>
               word_extract_itself
                 (fcpML.ITSELF (numML.fromDecString"8")) (fromString"7")
                 ZERO data
          | false =>
               (case
                  word_eq oareg
                    (n2w_itself
                       (ONE,(fcpML.ITSELF (numML.fromDecString"2"))))
                of true =>
                      word_extract_itself
                        (fcpML.ITSELF (numML.fromDecString"8"))
                        (fromString"15") (fromString"8") data
                 | false =>
                      (case
                         word_eq oareg
                           (n2w_itself
                              (TWO,(fcpML.ITSELF (numML.fromDecString"2"))))
                       of true =>
                             word_extract_itself
                               (fcpML.ITSELF (numML.fromDecString"8"))
                               (fromString"23") (fromString"16") data
                        | false =>
                             word_extract_itself
                               (fcpML.ITSELF (numML.fromDecString"8"))
                               (fromString"31") (fromString"24") data))
    
  fun FORMAT fmt oareg data =
        case fmt
         of SignedByte =>
               sw2sw_itself (fcpML.ITSELF (numML.fromDecString"32"))
                 (GET_BYTE oareg data)
          | UnsignedByte =>
               w2w_itself (fcpML.ITSELF (numML.fromDecString"32"))
                 (GET_BYTE oareg data)
          | SignedHalfWord =>
               sw2sw_itself (fcpML.ITSELF (numML.fromDecString"32"))
                 (GET_HALF oareg data)
          | UnsignedHalfWord =>
               w2w_itself (fcpML.ITSELF (numML.fromDecString"32"))
                 (GET_HALF oareg data)
          | UnsignedWord =>
               word_ror data ( *  (fromString"8") (w2n oareg))
    
  fun SET_BYTE oareg b w =
        word_modify (fn i => fn x =>
          < i (fromString"8")
          andalso
          (if word_eq oareg
                (n2w_itself
                   (ZERO,(fcpML.ITSELF (numML.fromDecString"2"))))
             then index b i else x)
          orelse
          ((<= (fromString"8") i andalso < i (fromString"16"))
           andalso
           (if word_eq oareg
                 (n2w_itself
                    (ONE,(fcpML.ITSELF (numML.fromDecString"2"))))
              then index b (- i (fromString"8")) else x)
           orelse
           ((<= (fromString"16") i andalso < i (fromString"24"))
            andalso
            (if word_eq oareg
                  (n2w_itself
                     (TWO,(fcpML.ITSELF (numML.fromDecString"2"))))
               then index b (- i (fromString"16")) else x)
            orelse
            (<= (fromString"24") i andalso < i (fromString"32"))
            andalso
            (if word_eq oareg
                  (n2w_itself
                     ((
                      fromString
                      "3"
                      ),(fcpML.ITSELF (numML.fromDecString"2"))))
               then index b (- i (fromString"24")) else x)))) w
    
  fun SET_HALF oareg hw w =
        word_modify (fn i => fn x =>
          < i (fromString"16")
          andalso
          (if not oareg then index hw i else x)
          orelse
          (<= (fromString"16") i andalso < i (fromString"32"))
          andalso
          (if oareg then index hw (- i (fromString"16")) else x)) w
    
  fun MEM_WRITE_BYTE mem addr word =
        let val addr30 = ADDR30 addr
        in
           mem_write mem addr30
             (SET_BYTE
                (word_extract_itself
                   (fcpML.ITSELF (numML.fromDecString"2")) ONE ZERO
                   addr) word (mem_read (mem,addr30)))
        end
    
  fun MEM_WRITE_HALF mem addr word =
        let val addr30 = ADDR30 addr
        in
           mem_write mem addr30
             (SET_HALF (index addr ONE) word (mem_read (mem,addr30)))
        end
    
  fun MEM_WRITE_WORD mem addr word = mem_write mem (ADDR30 addr) word
    
  fun MEM_WRITE mem addr d =
        case d
         of Byte(b) => MEM_WRITE_BYTE mem addr b
          | Half(hw) => MEM_WRITE_HALF mem addr hw
          | Word(w) => MEM_WRITE_WORD mem addr w
    
end
