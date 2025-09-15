import { fileUtils } from '../../_11ty/filters.js';

export default {
  eleventyNavigation: {
    order: 10,
    parent: "demo"
  },
  eleventyComputed: {
    title : (data) =>
      data.title ? data.title : fileUtils.name(data.page.inputPath),
    layout: (data) =>
      'md' === fileUtils.ext(data.page.inputPath) ? "index-page" :
      'v' === fileUtils.ext(data.page.inputPath) ? "demo-layout" : "page",
    eleventyNavigation: {
      title: (data) => data.title,
      order: (data) =>
        'hpp' === fileUtils.ext(data.page.inputPath) ?  0 :
        'cpp' === fileUtils.ext(data.page.inputPath) ? 10 :
        fileUtils.name(data.page.inputPath).lastIndexOf('spec') != -1  ? 20 : 30
    }
  }
};
