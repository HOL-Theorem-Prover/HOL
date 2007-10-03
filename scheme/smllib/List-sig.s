[loading standard basis library]
[processing /usr/local/mosml/src/mosmllib/List.sig]
(Program /usr/local/mosml/src/mosmllib/List.sig:1.0.126.4
  (SIGDECTopDec /usr/local/mosml/src/mosmllib/List.sig:1.0.126.3
    (SigDec /usr/local/mosml/src/mosmllib/List.sig:1.0.126.3
      (SigBind /usr/local/mosml/src/mosmllib/List.sig:1.10.126.3
        (SigId List)
        (SIGSigExp /usr/local/mosml/src/mosmllib/List.sig:2.0.126.3
          (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:6.0.126.0
            (DATATYPE2Spec /usr/local/mosml/src/mosmllib/List.sig:6.0.6.29
              (TyCon list)
              (LongTyCon list)
            )
            (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:8.0.126.0
              (EXCEPTIONSpec /usr/local/mosml/src/mosmllib/List.sig:8.0.10.0
                (ExDesc /usr/local/mosml/src/mosmllib/List.sig:8.10.10.0
                  (VId Empty)
                )
              )
              (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:10.0.126.0
                (VALSpec /usr/local/mosml/src/mosmllib/List.sig:10.0.11.0
                  (ValDesc /usr/local/mosml/src/mosmllib/List.sig:10.4.11.0
                    (VId null)
                    (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:10.17.10.32
                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:10.17.10.24
                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:10.17.10.19
                          (VARTy /usr/local/mosml/src/mosmllib/List.sig:10.17.10.19
                            (TyVar 'a)
                          )
                        )
                        (LongTyCon list)
                      )
                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:10.28.10.32
                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:10.28.10.28
                        )
                        (LongTyCon bool)
                      )
                    )
                  )
                )
                (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:11.0.126.0
                  (VALSpec /usr/local/mosml/src/mosmllib/List.sig:11.0.12.0
                    (ValDesc /usr/local/mosml/src/mosmllib/List.sig:11.4.12.0
                      (VId hd)
                      (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:11.17.11.30
                        (CONTy /usr/local/mosml/src/mosmllib/List.sig:11.17.11.24
                          (Tyseq /usr/local/mosml/src/mosmllib/List.sig:11.17.11.19
                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:11.17.11.19
                              (TyVar 'a)
                            )
                          )
                          (LongTyCon list)
                        )
                        (VARTy /usr/local/mosml/src/mosmllib/List.sig:11.28.11.30
                          (TyVar 'a)
                        )
                      )
                    )
                  )
                  (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:12.0.126.0
                    (VALSpec /usr/local/mosml/src/mosmllib/List.sig:12.0.13.0
                      (ValDesc /usr/local/mosml/src/mosmllib/List.sig:12.4.13.0
                        (VId tl)
                        (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:12.17.12.35
                          (CONTy /usr/local/mosml/src/mosmllib/List.sig:12.17.12.24
                            (Tyseq /usr/local/mosml/src/mosmllib/List.sig:12.17.12.19
                              (VARTy /usr/local/mosml/src/mosmllib/List.sig:12.17.12.19
                                (TyVar 'a)
                              )
                            )
                            (LongTyCon list)
                          )
                          (CONTy /usr/local/mosml/src/mosmllib/List.sig:12.28.12.35
                            (Tyseq /usr/local/mosml/src/mosmllib/List.sig:12.28.12.30
                              (VARTy /usr/local/mosml/src/mosmllib/List.sig:12.28.12.30
                                (TyVar 'a)
                              )
                            )
                            (LongTyCon list)
                          )
                        )
                      )
                    )
                    (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:13.0.126.0
                      (VALSpec /usr/local/mosml/src/mosmllib/List.sig:13.0.15.0
                        (ValDesc /usr/local/mosml/src/mosmllib/List.sig:13.4.15.0
                          (VId last)
                          (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:13.17.13.30
                            (CONTy /usr/local/mosml/src/mosmllib/List.sig:13.17.13.24
                              (Tyseq /usr/local/mosml/src/mosmllib/List.sig:13.17.13.19
                                (VARTy /usr/local/mosml/src/mosmllib/List.sig:13.17.13.19
                                  (TyVar 'a)
                                )
                              )
                              (LongTyCon list)
                            )
                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:13.28.13.30
                              (TyVar 'a)
                            )
                          )
                        )
                      )
                      (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:15.0.126.0
                        (VALSpec /usr/local/mosml/src/mosmllib/List.sig:15.0.16.0
                          (ValDesc /usr/local/mosml/src/mosmllib/List.sig:15.4.16.0
                            (VId nth)
                            (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:15.17.15.36
                              (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:15.17.15.30
                                (TyRow /usr/local/mosml/src/mosmllib/List.sig:15.17.15.30
                                  (Lab 1)
                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:15.17.15.24
                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:15.17.15.19
                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:15.17.15.19
                                        (TyVar 'a)
                                      )
                                    )
                                    (LongTyCon list)
                                  )
                                  (TyRow /usr/local/mosml/src/mosmllib/List.sig:15.17.15.30
                                    (Lab 2)
                                    (CONTy /usr/local/mosml/src/mosmllib/List.sig:15.27.15.30
                                      (Tyseq /usr/local/mosml/src/mosmllib/List.sig:15.27.15.27
                                      )
                                      (LongTyCon int)
                                    )
                                  )
                                )
                              )
                              (VARTy /usr/local/mosml/src/mosmllib/List.sig:15.34.15.36
                                (TyVar 'a)
                              )
                            )
                          )
                        )
                        (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:16.0.126.0
                          (VALSpec /usr/local/mosml/src/mosmllib/List.sig:16.0.17.0
                            (ValDesc /usr/local/mosml/src/mosmllib/List.sig:16.4.17.0
                              (VId take)
                              (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:16.17.16.41
                                (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:16.17.16.30
                                  (TyRow /usr/local/mosml/src/mosmllib/List.sig:16.17.16.30
                                    (Lab 1)
                                    (CONTy /usr/local/mosml/src/mosmllib/List.sig:16.17.16.24
                                      (Tyseq /usr/local/mosml/src/mosmllib/List.sig:16.17.16.19
                                        (VARTy /usr/local/mosml/src/mosmllib/List.sig:16.17.16.19
                                          (TyVar 'a)
                                        )
                                      )
                                      (LongTyCon list)
                                    )
                                    (TyRow /usr/local/mosml/src/mosmllib/List.sig:16.17.16.30
                                      (Lab 2)
                                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:16.27.16.30
                                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:16.27.16.27
                                        )
                                        (LongTyCon int)
                                      )
                                    )
                                  )
                                )
                                (CONTy /usr/local/mosml/src/mosmllib/List.sig:16.34.16.41
                                  (Tyseq /usr/local/mosml/src/mosmllib/List.sig:16.34.16.36
                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:16.34.16.36
                                      (TyVar 'a)
                                    )
                                  )
                                  (LongTyCon list)
                                )
                              )
                            )
                          )
                          (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:17.0.126.0
                            (VALSpec /usr/local/mosml/src/mosmllib/List.sig:17.0.19.0
                              (ValDesc /usr/local/mosml/src/mosmllib/List.sig:17.4.19.0
                                (VId drop)
                                (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:17.17.17.41
                                  (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:17.17.17.30
                                    (TyRow /usr/local/mosml/src/mosmllib/List.sig:17.17.17.30
                                      (Lab 1)
                                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:17.17.17.24
                                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:17.17.17.19
                                          (VARTy /usr/local/mosml/src/mosmllib/List.sig:17.17.17.19
                                            (TyVar 'a)
                                          )
                                        )
                                        (LongTyCon list)
                                      )
                                      (TyRow /usr/local/mosml/src/mosmllib/List.sig:17.17.17.30
                                        (Lab 2)
                                        (CONTy /usr/local/mosml/src/mosmllib/List.sig:17.27.17.30
                                          (Tyseq /usr/local/mosml/src/mosmllib/List.sig:17.27.17.27
                                          )
                                          (LongTyCon int)
                                        )
                                      )
                                    )
                                  )
                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:17.34.17.41
                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:17.34.17.36
                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:17.34.17.36
                                        (TyVar 'a)
                                      )
                                    )
                                    (LongTyCon list)
                                  )
                                )
                              )
                            )
                            (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:19.0.126.0
                              (VALSpec /usr/local/mosml/src/mosmllib/List.sig:19.0.21.0
                                (ValDesc /usr/local/mosml/src/mosmllib/List.sig:19.4.21.0
                                  (VId length)
                                  (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:19.17.19.31
                                    (CONTy /usr/local/mosml/src/mosmllib/List.sig:19.17.19.24
                                      (Tyseq /usr/local/mosml/src/mosmllib/List.sig:19.17.19.19
                                        (VARTy /usr/local/mosml/src/mosmllib/List.sig:19.17.19.19
                                          (TyVar 'a)
                                        )
                                      )
                                      (LongTyCon list)
                                    )
                                    (CONTy /usr/local/mosml/src/mosmllib/List.sig:19.28.19.31
                                      (Tyseq /usr/local/mosml/src/mosmllib/List.sig:19.28.19.28
                                      )
                                      (LongTyCon int)
                                    )
                                  )
                                )
                              )
                              (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:21.0.126.0
                                (VALSpec /usr/local/mosml/src/mosmllib/List.sig:21.0.23.0
                                  (ValDesc /usr/local/mosml/src/mosmllib/List.sig:21.4.23.0
                                    (VId rev)
                                    (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:21.17.21.35
                                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:21.17.21.24
                                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:21.17.21.19
                                          (VARTy /usr/local/mosml/src/mosmllib/List.sig:21.17.21.19
                                            (TyVar 'a)
                                          )
                                        )
                                        (LongTyCon list)
                                      )
                                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:21.28.21.35
                                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:21.28.21.30
                                          (VARTy /usr/local/mosml/src/mosmllib/List.sig:21.28.21.30
                                            (TyVar 'a)
                                          )
                                        )
                                        (LongTyCon list)
                                      )
                                    )
                                  )
                                )
                                (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:23.0.126.0
                                  (VALSpec /usr/local/mosml/src/mosmllib/List.sig:23.0.24.0
                                    (ValDesc /usr/local/mosml/src/mosmllib/List.sig:23.4.24.0
                                      (VId @)
                                      (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:23.17.23.45
                                        (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:23.17.23.34
                                          (TyRow /usr/local/mosml/src/mosmllib/List.sig:23.17.23.34
                                            (Lab 1)
                                            (CONTy /usr/local/mosml/src/mosmllib/List.sig:23.17.23.24
                                              (Tyseq /usr/local/mosml/src/mosmllib/List.sig:23.17.23.19
                                                (VARTy /usr/local/mosml/src/mosmllib/List.sig:23.17.23.19
                                                  (TyVar 'a)
                                                )
                                              )
                                              (LongTyCon list)
                                            )
                                            (TyRow /usr/local/mosml/src/mosmllib/List.sig:23.17.23.34
                                              (Lab 2)
                                              (CONTy /usr/local/mosml/src/mosmllib/List.sig:23.27.23.34
                                                (Tyseq /usr/local/mosml/src/mosmllib/List.sig:23.27.23.29
                                                  (VARTy /usr/local/mosml/src/mosmllib/List.sig:23.27.23.29
                                                    (TyVar 'a)
                                                  )
                                                )
                                                (LongTyCon list)
                                              )
                                            )
                                          )
                                        )
                                        (CONTy /usr/local/mosml/src/mosmllib/List.sig:23.38.23.45
                                          (Tyseq /usr/local/mosml/src/mosmllib/List.sig:23.38.23.40
                                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:23.38.23.40
                                              (TyVar 'a)
                                            )
                                          )
                                          (LongTyCon list)
                                        )
                                      )
                                    )
                                  )
                                  (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:24.0.126.0
                                    (VALSpec /usr/local/mosml/src/mosmllib/List.sig:24.0.25.0
                                      (ValDesc /usr/local/mosml/src/mosmllib/List.sig:24.4.25.0
                                        (VId concat)
                                        (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:24.17.24.40
                                          (CONTy /usr/local/mosml/src/mosmllib/List.sig:24.17.24.29
                                            (Tyseq /usr/local/mosml/src/mosmllib/List.sig:24.17.24.24
                                              (CONTy /usr/local/mosml/src/mosmllib/List.sig:24.17.24.24
                                                (Tyseq /usr/local/mosml/src/mosmllib/List.sig:24.17.24.19
                                                  (VARTy /usr/local/mosml/src/mosmllib/List.sig:24.17.24.19
                                                    (TyVar 'a)
                                                  )
                                                )
                                                (LongTyCon list)
                                              )
                                            )
                                            (LongTyCon list)
                                          )
                                          (CONTy /usr/local/mosml/src/mosmllib/List.sig:24.33.24.40
                                            (Tyseq /usr/local/mosml/src/mosmllib/List.sig:24.33.24.35
                                              (VARTy /usr/local/mosml/src/mosmllib/List.sig:24.33.24.35
                                                (TyVar 'a)
                                              )
                                            )
                                            (LongTyCon list)
                                          )
                                        )
                                      )
                                    )
                                    (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:25.0.126.0
                                      (VALSpec /usr/local/mosml/src/mosmllib/List.sig:25.0.27.0
                                        (ValDesc /usr/local/mosml/src/mosmllib/List.sig:25.4.27.0
                                          (VId revAppend)
                                          (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:25.17.25.45
                                            (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:25.17.25.34
                                              (TyRow /usr/local/mosml/src/mosmllib/List.sig:25.17.25.34
                                                (Lab 1)
                                                (CONTy /usr/local/mosml/src/mosmllib/List.sig:25.17.25.24
                                                  (Tyseq /usr/local/mosml/src/mosmllib/List.sig:25.17.25.19
                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:25.17.25.19
                                                      (TyVar 'a)
                                                    )
                                                  )
                                                  (LongTyCon list)
                                                )
                                                (TyRow /usr/local/mosml/src/mosmllib/List.sig:25.17.25.34
                                                  (Lab 2)
                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:25.27.25.34
                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:25.27.25.29
                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:25.27.25.29
                                                        (TyVar 'a)
                                                      )
                                                    )
                                                    (LongTyCon list)
                                                  )
                                                )
                                              )
                                            )
                                            (CONTy /usr/local/mosml/src/mosmllib/List.sig:25.38.25.45
                                              (Tyseq /usr/local/mosml/src/mosmllib/List.sig:25.38.25.40
                                                (VARTy /usr/local/mosml/src/mosmllib/List.sig:25.38.25.40
                                                  (TyVar 'a)
                                                )
                                              )
                                              (LongTyCon list)
                                            )
                                          )
                                        )
                                      )
                                      (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:27.0.126.0
                                        (VALSpec /usr/local/mosml/src/mosmllib/List.sig:27.0.28.0
                                          (ValDesc /usr/local/mosml/src/mosmllib/List.sig:27.4.28.0
                                            (VId app)
                                            (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:27.17.27.48
                                              (PARTy /usr/local/mosml/src/mosmllib/List.sig:27.17.27.29
                                                (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:27.18.27.28
                                                  (VARTy /usr/local/mosml/src/mosmllib/List.sig:27.18.27.20
                                                    (TyVar 'a)
                                                  )
                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:27.24.27.28
                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:27.24.27.24
                                                    )
                                                    (LongTyCon unit)
                                                  )
                                                )
                                              )
                                              (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:27.33.27.48
                                                (CONTy /usr/local/mosml/src/mosmllib/List.sig:27.33.27.40
                                                  (Tyseq /usr/local/mosml/src/mosmllib/List.sig:27.33.27.35
                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:27.33.27.35
                                                      (TyVar 'a)
                                                    )
                                                  )
                                                  (LongTyCon list)
                                                )
                                                (CONTy /usr/local/mosml/src/mosmllib/List.sig:27.44.27.48
                                                  (Tyseq /usr/local/mosml/src/mosmllib/List.sig:27.44.27.44
                                                  )
                                                  (LongTyCon unit)
                                                )
                                              )
                                            )
                                          )
                                        )
                                        (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:28.0.126.0
                                          (VALSpec /usr/local/mosml/src/mosmllib/List.sig:28.0.29.0
                                            (ValDesc /usr/local/mosml/src/mosmllib/List.sig:28.4.29.0
                                              (VId map)
                                              (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:28.17.28.49
                                                (PARTy /usr/local/mosml/src/mosmllib/List.sig:28.17.28.27
                                                  (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:28.18.28.26
                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:28.18.28.20
                                                      (TyVar 'a)
                                                    )
                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:28.24.28.26
                                                      (TyVar 'b)
                                                    )
                                                  )
                                                )
                                                (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:28.31.28.49
                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:28.31.28.38
                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:28.31.28.33
                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:28.31.28.33
                                                        (TyVar 'a)
                                                      )
                                                    )
                                                    (LongTyCon list)
                                                  )
                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:28.42.28.49
                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:28.42.28.44
                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:28.42.28.44
                                                        (TyVar 'b)
                                                      )
                                                    )
                                                    (LongTyCon list)
                                                  )
                                                )
                                              )
                                            )
                                          )
                                          (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:29.0.126.0
                                            (VALSpec /usr/local/mosml/src/mosmllib/List.sig:29.0.31.0
                                              (ValDesc /usr/local/mosml/src/mosmllib/List.sig:29.4.31.0
                                                (VId mapPartial)
                                                (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:29.17.29.56
                                                  (PARTy /usr/local/mosml/src/mosmllib/List.sig:29.17.29.34
                                                    (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:29.18.29.33
                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:29.18.29.20
                                                        (TyVar 'a)
                                                      )
                                                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:29.24.29.33
                                                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:29.24.29.26
                                                          (VARTy /usr/local/mosml/src/mosmllib/List.sig:29.24.29.26
                                                            (TyVar 'b)
                                                          )
                                                        )
                                                        (LongTyCon option)
                                                      )
                                                    )
                                                  )
                                                  (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:29.38.29.56
                                                    (CONTy /usr/local/mosml/src/mosmllib/List.sig:29.38.29.45
                                                      (Tyseq /usr/local/mosml/src/mosmllib/List.sig:29.38.29.40
                                                        (VARTy /usr/local/mosml/src/mosmllib/List.sig:29.38.29.40
                                                          (TyVar 'a)
                                                        )
                                                      )
                                                      (LongTyCon list)
                                                    )
                                                    (CONTy /usr/local/mosml/src/mosmllib/List.sig:29.49.29.56
                                                      (Tyseq /usr/local/mosml/src/mosmllib/List.sig:29.49.29.51
                                                        (VARTy /usr/local/mosml/src/mosmllib/List.sig:29.49.29.51
                                                          (TyVar 'b)
                                                        )
                                                      )
                                                      (LongTyCon list)
                                                    )
                                                  )
                                                )
                                              )
                                            )
                                            (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:31.0.126.0
                                              (VALSpec /usr/local/mosml/src/mosmllib/List.sig:31.0.32.0
                                                (ValDesc /usr/local/mosml/src/mosmllib/List.sig:31.4.32.0
                                                  (VId find)
                                                  (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:31.17.31.53
                                                    (PARTy /usr/local/mosml/src/mosmllib/List.sig:31.17.31.29
                                                      (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:31.18.31.28
                                                        (VARTy /usr/local/mosml/src/mosmllib/List.sig:31.18.31.20
                                                          (TyVar 'a)
                                                        )
                                                        (CONTy /usr/local/mosml/src/mosmllib/List.sig:31.24.31.28
                                                          (Tyseq /usr/local/mosml/src/mosmllib/List.sig:31.24.31.24
                                                          )
                                                          (LongTyCon bool)
                                                        )
                                                      )
                                                    )
                                                    (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:31.33.31.53
                                                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:31.33.31.40
                                                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:31.33.31.35
                                                          (VARTy /usr/local/mosml/src/mosmllib/List.sig:31.33.31.35
                                                            (TyVar 'a)
                                                          )
                                                        )
                                                        (LongTyCon list)
                                                      )
                                                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:31.44.31.53
                                                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:31.44.31.46
                                                          (VARTy /usr/local/mosml/src/mosmllib/List.sig:31.44.31.46
                                                            (TyVar 'a)
                                                          )
                                                        )
                                                        (LongTyCon option)
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                              (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:32.0.126.0
                                                (VALSpec /usr/local/mosml/src/mosmllib/List.sig:32.0.33.0
                                                  (ValDesc /usr/local/mosml/src/mosmllib/List.sig:32.4.33.0
                                                    (VId filter)
                                                    (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:32.17.32.51
                                                      (PARTy /usr/local/mosml/src/mosmllib/List.sig:32.17.32.29
                                                        (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:32.18.32.28
                                                          (VARTy /usr/local/mosml/src/mosmllib/List.sig:32.18.32.20
                                                            (TyVar 'a)
                                                          )
                                                          (CONTy /usr/local/mosml/src/mosmllib/List.sig:32.24.32.28
                                                            (Tyseq /usr/local/mosml/src/mosmllib/List.sig:32.24.32.24
                                                            )
                                                            (LongTyCon bool)
                                                          )
                                                        )
                                                      )
                                                      (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:32.33.32.51
                                                        (CONTy /usr/local/mosml/src/mosmllib/List.sig:32.33.32.40
                                                          (Tyseq /usr/local/mosml/src/mosmllib/List.sig:32.33.32.35
                                                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:32.33.32.35
                                                              (TyVar 'a)
                                                            )
                                                          )
                                                          (LongTyCon list)
                                                        )
                                                        (CONTy /usr/local/mosml/src/mosmllib/List.sig:32.44.32.51
                                                          (Tyseq /usr/local/mosml/src/mosmllib/List.sig:32.44.32.46
                                                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:32.44.32.46
                                                              (TyVar 'a)
                                                            )
                                                          )
                                                          (LongTyCon list)
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                                (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:33.0.126.0
                                                  (VALSpec /usr/local/mosml/src/mosmllib/List.sig:33.0.35.0
                                                    (ValDesc /usr/local/mosml/src/mosmllib/List.sig:33.4.35.0
                                                      (VId partition)
                                                      (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:33.17.33.64
                                                        (PARTy /usr/local/mosml/src/mosmllib/List.sig:33.17.33.30
                                                          (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:33.18.33.28
                                                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:33.18.33.20
                                                              (TyVar 'a)
                                                            )
                                                            (CONTy /usr/local/mosml/src/mosmllib/List.sig:33.24.33.28
                                                              (Tyseq /usr/local/mosml/src/mosmllib/List.sig:33.24.33.24
                                                              )
                                                              (LongTyCon bool)
                                                            )
                                                          )
                                                        )
                                                        (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:33.34.33.64
                                                          (CONTy /usr/local/mosml/src/mosmllib/List.sig:33.34.33.41
                                                            (Tyseq /usr/local/mosml/src/mosmllib/List.sig:33.34.33.36
                                                              (VARTy /usr/local/mosml/src/mosmllib/List.sig:33.34.33.36
                                                                (TyVar 'a)
                                                              )
                                                            )
                                                            (LongTyCon list)
                                                          )
                                                          (PARTy /usr/local/mosml/src/mosmllib/List.sig:33.45.33.64
                                                            (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:33.46.33.63
                                                              (TyRow /usr/local/mosml/src/mosmllib/List.sig:33.46.33.63
                                                                (Lab 1)
                                                                (CONTy /usr/local/mosml/src/mosmllib/List.sig:33.46.33.53
                                                                  (Tyseq /usr/local/mosml/src/mosmllib/List.sig:33.46.33.48
                                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:33.46.33.48
                                                                      (TyVar 'a)
                                                                    )
                                                                  )
                                                                  (LongTyCon list)
                                                                )
                                                                (TyRow /usr/local/mosml/src/mosmllib/List.sig:33.46.33.63
                                                                  (Lab 2)
                                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:33.56.33.63
                                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:33.56.33.58
                                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:33.56.33.58
                                                                        (TyVar 'a)
                                                                      )
                                                                    )
                                                                    (LongTyCon list)
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  )
                                                  (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:35.0.126.0
                                                    (VALSpec /usr/local/mosml/src/mosmllib/List.sig:35.0.36.0
                                                      (ValDesc /usr/local/mosml/src/mosmllib/List.sig:35.4.36.0
                                                        (VId foldr)
                                                        (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:35.17.35.55
                                                          (PARTy /usr/local/mosml/src/mosmllib/List.sig:35.17.35.32
                                                            (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:35.18.35.31
                                                              (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:35.18.35.25
                                                                (TyRow /usr/local/mosml/src/mosmllib/List.sig:35.18.35.25
                                                                  (Lab 1)
                                                                  (VARTy /usr/local/mosml/src/mosmllib/List.sig:35.18.35.20
                                                                    (TyVar 'a)
                                                                  )
                                                                  (TyRow /usr/local/mosml/src/mosmllib/List.sig:35.18.35.25
                                                                    (Lab 2)
                                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:35.23.35.25
                                                                      (TyVar 'b)
                                                                    )
                                                                  )
                                                                )
                                                              )
                                                              (VARTy /usr/local/mosml/src/mosmllib/List.sig:35.29.35.31
                                                                (TyVar 'b)
                                                              )
                                                            )
                                                          )
                                                          (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:35.36.35.55
                                                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:35.36.35.38
                                                              (TyVar 'b)
                                                            )
                                                            (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:35.42.35.55
                                                              (CONTy /usr/local/mosml/src/mosmllib/List.sig:35.42.35.49
                                                                (Tyseq /usr/local/mosml/src/mosmllib/List.sig:35.42.35.44
                                                                  (VARTy /usr/local/mosml/src/mosmllib/List.sig:35.42.35.44
                                                                    (TyVar 'a)
                                                                  )
                                                                )
                                                                (LongTyCon list)
                                                              )
                                                              (VARTy /usr/local/mosml/src/mosmllib/List.sig:35.53.35.55
                                                                (TyVar 'b)
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                    (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:36.0.126.0
                                                      (VALSpec /usr/local/mosml/src/mosmllib/List.sig:36.0.38.0
                                                        (ValDesc /usr/local/mosml/src/mosmllib/List.sig:36.4.38.0
                                                          (VId foldl)
                                                          (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:36.17.36.55
                                                            (PARTy /usr/local/mosml/src/mosmllib/List.sig:36.17.36.32
                                                              (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:36.18.36.31
                                                                (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:36.18.36.25
                                                                  (TyRow /usr/local/mosml/src/mosmllib/List.sig:36.18.36.25
                                                                    (Lab 1)
                                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:36.18.36.20
                                                                      (TyVar 'a)
                                                                    )
                                                                    (TyRow /usr/local/mosml/src/mosmllib/List.sig:36.18.36.25
                                                                      (Lab 2)
                                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:36.23.36.25
                                                                        (TyVar 'b)
                                                                      )
                                                                    )
                                                                  )
                                                                )
                                                                (VARTy /usr/local/mosml/src/mosmllib/List.sig:36.29.36.31
                                                                  (TyVar 'b)
                                                                )
                                                              )
                                                            )
                                                            (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:36.36.36.55
                                                              (VARTy /usr/local/mosml/src/mosmllib/List.sig:36.36.36.38
                                                                (TyVar 'b)
                                                              )
                                                              (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:36.42.36.55
                                                                (CONTy /usr/local/mosml/src/mosmllib/List.sig:36.42.36.49
                                                                  (Tyseq /usr/local/mosml/src/mosmllib/List.sig:36.42.36.44
                                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:36.42.36.44
                                                                      (TyVar 'a)
                                                                    )
                                                                  )
                                                                  (LongTyCon list)
                                                                )
                                                                (VARTy /usr/local/mosml/src/mosmllib/List.sig:36.53.36.55
                                                                  (TyVar 'b)
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                      (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:38.0.126.0
                                                        (VALSpec /usr/local/mosml/src/mosmllib/List.sig:38.0.39.0
                                                          (ValDesc /usr/local/mosml/src/mosmllib/List.sig:38.4.39.0
                                                            (VId exists)
                                                            (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:38.17.38.48
                                                              (PARTy /usr/local/mosml/src/mosmllib/List.sig:38.17.38.29
                                                                (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:38.18.38.28
                                                                  (VARTy /usr/local/mosml/src/mosmllib/List.sig:38.18.38.20
                                                                    (TyVar 'a)
                                                                  )
                                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:38.24.38.28
                                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:38.24.38.24
                                                                    )
                                                                    (LongTyCon bool)
                                                                  )
                                                                )
                                                              )
                                                              (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:38.33.38.48
                                                                (CONTy /usr/local/mosml/src/mosmllib/List.sig:38.33.38.40
                                                                  (Tyseq /usr/local/mosml/src/mosmllib/List.sig:38.33.38.35
                                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:38.33.38.35
                                                                      (TyVar 'a)
                                                                    )
                                                                  )
                                                                  (LongTyCon list)
                                                                )
                                                                (CONTy /usr/local/mosml/src/mosmllib/List.sig:38.44.38.48
                                                                  (Tyseq /usr/local/mosml/src/mosmllib/List.sig:38.44.38.44
                                                                  )
                                                                  (LongTyCon bool)
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                        (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:39.0.126.0
                                                          (VALSpec /usr/local/mosml/src/mosmllib/List.sig:39.0.41.0
                                                            (ValDesc /usr/local/mosml/src/mosmllib/List.sig:39.4.41.0
                                                              (VId all)
                                                              (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:39.17.39.48
                                                                (PARTy /usr/local/mosml/src/mosmllib/List.sig:39.17.39.29
                                                                  (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:39.18.39.28
                                                                    (VARTy /usr/local/mosml/src/mosmllib/List.sig:39.18.39.20
                                                                      (TyVar 'a)
                                                                    )
                                                                    (CONTy /usr/local/mosml/src/mosmllib/List.sig:39.24.39.28
                                                                      (Tyseq /usr/local/mosml/src/mosmllib/List.sig:39.24.39.24
                                                                      )
                                                                      (LongTyCon bool)
                                                                    )
                                                                  )
                                                                )
                                                                (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:39.33.39.48
                                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:39.33.39.40
                                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:39.33.39.35
                                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:39.33.39.35
                                                                        (TyVar 'a)
                                                                      )
                                                                    )
                                                                    (LongTyCon list)
                                                                  )
                                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:39.44.39.48
                                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:39.44.39.44
                                                                    )
                                                                    (LongTyCon bool)
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                          (SEQSpec /usr/local/mosml/src/mosmllib/List.sig:41.0.126.0
                                                            (VALSpec /usr/local/mosml/src/mosmllib/List.sig:41.0.43.0
                                                              (ValDesc /usr/local/mosml/src/mosmllib/List.sig:41.4.43.0
                                                                (VId tabulate)
                                                                (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:41.17.41.45
                                                                  (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:41.17.41.34
                                                                    (TyRow /usr/local/mosml/src/mosmllib/List.sig:41.17.41.34
                                                                      (Lab 1)
                                                                      (CONTy /usr/local/mosml/src/mosmllib/List.sig:41.17.41.20
                                                                        (Tyseq /usr/local/mosml/src/mosmllib/List.sig:41.17.41.17
                                                                        )
                                                                        (LongTyCon int)
                                                                      )
                                                                      (TyRow /usr/local/mosml/src/mosmllib/List.sig:41.17.41.34
                                                                        (Lab 2)
                                                                        (PARTy /usr/local/mosml/src/mosmllib/List.sig:41.23.41.34
                                                                          (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:41.24.41.33
                                                                            (CONTy /usr/local/mosml/src/mosmllib/List.sig:41.24.41.27
                                                                              (Tyseq /usr/local/mosml/src/mosmllib/List.sig:41.24.41.24
                                                                              )
                                                                              (LongTyCon int)
                                                                            )
                                                                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:41.31.41.33
                                                                              (TyVar 'a)
                                                                            )
                                                                          )
                                                                        )
                                                                      )
                                                                    )
                                                                  )
                                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:41.38.41.45
                                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:41.38.41.40
                                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:41.38.41.40
                                                                        (TyVar 'a)
                                                                      )
                                                                    )
                                                                    (LongTyCon list)
                                                                  )
                                                                )
                                                              )
                                                            )
                                                            (VALSpec /usr/local/mosml/src/mosmllib/List.sig:43.0.126.0
                                                              (ValDesc /usr/local/mosml/src/mosmllib/List.sig:43.4.126.0
                                                                (VId getItem)
                                                                (ARROWTy /usr/local/mosml/src/mosmllib/List.sig:43.17.43.49
                                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:43.17.43.24
                                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:43.17.43.19
                                                                      (VARTy /usr/local/mosml/src/mosmllib/List.sig:43.17.43.19
                                                                        (TyVar 'a)
                                                                      )
                                                                    )
                                                                    (LongTyCon list)
                                                                  )
                                                                  (CONTy /usr/local/mosml/src/mosmllib/List.sig:43.28.43.49
                                                                    (Tyseq /usr/local/mosml/src/mosmllib/List.sig:43.28.43.42
                                                                      (PARTy /usr/local/mosml/src/mosmllib/List.sig:43.28.43.42
                                                                        (RECORDTy /usr/local/mosml/src/mosmllib/List.sig:43.29.43.41
                                                                          (TyRow /usr/local/mosml/src/mosmllib/List.sig:43.29.43.41
                                                                            (Lab 1)
                                                                            (VARTy /usr/local/mosml/src/mosmllib/List.sig:43.29.43.31
                                                                              (TyVar 'a)
                                                                            )
                                                                            (TyRow /usr/local/mosml/src/mosmllib/List.sig:43.29.43.41
                                                                              (Lab 2)
                                                                              (CONTy /usr/local/mosml/src/mosmllib/List.sig:43.34.43.41
                                                                                (Tyseq /usr/local/mosml/src/mosmllib/List.sig:43.34.43.36
                                                                                  (VARTy /usr/local/mosml/src/mosmllib/List.sig:43.34.43.36
                                                                                    (TyVar 'a)
                                                                                  )
                                                                                )
                                                                                (LongTyCon list)
                                                                              )
                                                                            )
                                                                          )
                                                                        )
                                                                      )
                                                                    )
                                                                    (LongTyCon option)
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)
