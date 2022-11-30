// use crate::*;

// #[test]
// fn decreasing_range_inclusive_test() {
//     let unallocated_regions = [None, None, None, None, None, None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None];
//     let mut chunk_list = convert_unallocated_regions_to_chunks(unallocated_regions);
//     assert!(chunk_list.is_ok());
//     let mut chunk_list = chunk_list.unwrap();

//     let chunk1 = create_new_trusted_chunk(RangeInclusive::new(10, 0), &mut chunk_list);
//     assert!(chunk1.is_err());

//     let chunk2 = create_new_trusted_chunk(RangeInclusive::new(11, 7), &mut chunk_list);
//     assert!(chunk2.is_err());
// }

// #[test]
// fn disjoint_ranges() {
//     let unallocated_regions = [None, None, None, None, None, None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None];
//     let mut chunk_list = convert_unallocated_regions_to_chunks(unallocated_regions);
//     assert!(chunk_list.is_ok());
//     let mut chunk_list = chunk_list.unwrap();

//     let chunk1 = create_new_trusted_chunk(RangeInclusive::new(0, 10), &mut chunk_list);
//     assert!(chunk1.is_ok());

//     let chunk2 = create_new_trusted_chunk(RangeInclusive::new(11, 20), &mut chunk_list);
//     assert!(chunk2.is_ok());
// }


// #[test]
// fn equivalent_ranges() {
//     let unallocated_regions = [None, None, None, None, None, None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None];
//     let mut chunk_list = convert_unallocated_regions_to_chunks(unallocated_regions);
//     assert!(chunk_list.is_ok());
//     let mut chunk_list = chunk_list.unwrap();

//     let chunk1 = create_new_trusted_chunk(RangeInclusive::new(0, 10), &mut chunk_list);
//     assert!(chunk1.is_ok());

//     let chunk2 = create_new_trusted_chunk(RangeInclusive::new(0, 10), &mut chunk_list);
//     assert!(chunk2.is_err());
// }


// #[test]
// fn lower_bound_overlap() {
//     let unallocated_regions = [None, None, None, None, None, None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None];
//     let mut chunk_list = convert_unallocated_regions_to_chunks(unallocated_regions);
//     assert!(chunk_list.is_ok());
//     let mut chunk_list = chunk_list.unwrap();

//     let chunk1 = create_new_trusted_chunk(RangeInclusive::new(10, 20), &mut chunk_list);
//     assert!(chunk1.is_ok());

//     let chunk2 = create_new_trusted_chunk(RangeInclusive::new(0, 10), &mut chunk_list);
//     assert!(chunk2.is_err());

//     let chunk3 = create_new_trusted_chunk(RangeInclusive::new(0, 13), &mut chunk_list);
//     assert!(chunk3.is_err());
// }


// #[test]
// fn upper_bound_overlap() {
//     let unallocated_regions = [None, None, None, None, None, None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None, None, None, None,None, None, None, None, None,
//                                 None, None];
//     let mut chunk_list = convert_unallocated_regions_to_chunks(unallocated_regions);
//     assert!(chunk_list.is_ok());
//     let mut chunk_list = chunk_list.unwrap();

//     let chunk1 = create_new_trusted_chunk(RangeInclusive::new(10, 20), &mut chunk_list);
//     assert!(chunk1.is_ok());

//     let chunk2 = create_new_trusted_chunk(RangeInclusive::new(20, 30), &mut chunk_list);
//     assert!(chunk2.is_err());

//     let chunk3 = create_new_trusted_chunk(RangeInclusive::new(15, 30), &mut chunk_list);
//     assert!(chunk3.is_err());
// }